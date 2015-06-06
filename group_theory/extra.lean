/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
-- These belong in the library somewhere.
import data.list.basic data.finset.basic data.fintype.card

-- renamed and_imp_eq
-- theorem and_imp_curry (a b c : Prop) : (a ∧ b → c) = (a → b → c) :=
--        propext (iff.intro (λ Pl a b, Pl (and.intro a b))
--                           (λ Pr Pand, Pr (and.left Pand) (and.right Pand)))

-- changed to iff and named and_iff_right
-- theorem and_discharge_left {a b : Prop} : a → (a ∧ b) = b :=
--        assume Pa, propext (iff.intro (assume Pab, and.elim_right Pab)
--                                      (assume Pb, and.intro Pa Pb))

-- was already in the algebra.function as flip, but I renamed it to swap
-- definition swap {A B C : Type} (f : A → B → C) : B → A → C := λ x y, f y x

-- this is in algebra.order, not_lt_of_ge
-- lemma not_lt_of_le {a b : nat} : a ≤ b → ¬ b < a :=
--      assume aleb, not.intro (assume blta, lt.irrefl a (lt_of_le_of_lt aleb blta))

-- made iff
-- lemma injective_eq_inj_on_univ {f : A → B} : injective f = inj_on f univ :=

-- renamed to maps_to_univ_univ
-- lemma univ_maps_to_univ {f : A → B} : maps_to f univ univ :=

-- note: I now made the first two arguments to "injective f" implicit in the library
-- theorem injective_compose {g : B → C} {f : A → B} (Hg : injective g) (Hf : injective f) : injective (g ∘ f) :=

-- made iff
-- lemma surjective_eq_surj_on_univ {f : A → B} : surjective f = surj_on f univ univ :=

-- made iff
-- lemma bijective_eq_bij_on_univ {f : A → B} : bijective f = bij_on f univ univ :=

-- renamed injective_id, surjective_id, bijective_id
-- theorem id_is_inj : injective (@id A)
-- theorem id_is_surj : surjective (@id A)
-- theorem id_is_bij : bijective (@id A)

-- this doesn't require decidable equality, but it does require function extensionality
-- lemma left_inv_of_right_inv_of_inj
--      {A : Type} [h : decidable_eq A] {B : Type} {f : A → B} {g : B → A}
--      : injective f → f∘g = id → g∘f = id
-- instead, I put the version that does not require extensionality, in algebra.function,
--    right_inverse_of_injective_of_left_inverse
-- see also left_inverse_of_surjective_of_right_inverse
-- I also did the corresponding versions in set.function and set.map

-- this one seemed too special-purpose to me
-- lemma comm_one (a : A) : a*1 = 1*a

-- renamed mul_eq_one_iff_mul_eq_one
-- lemma comm_mul_eq_one (a b : A) : a*b = 1 = (b*a = 1) :=

-- renamed find_not_mem to not_mem_of_find_eq_length
-- renamed find_mem to find_lt_length


namespace list

-- useful for inverting function on a finite domain
section kth
open nat
variable {A : Type}

definition kth : ∀ k (l : list A), k < length l → A
| k []        := begin rewrite length_nil, intro Pltz, exact absurd Pltz !not_lt_zero end
| 0 (a::l)    := λ P, a
| (k+1) (a::l):= by rewrite length_cons; intro Plt; exact kth k l (lt_of_succ_lt_succ Plt)

lemma kth_zero_of_cons {a} (l : list A) (P : 0 < length (a::l)) : kth 0 (a::l) P = a :=
      rfl
lemma kth_succ_of_cons {a} k (l : list A) (P : k+1 < length (a::l)) : kth (succ k) (a::l) P = kth k l (lt_of_succ_lt_succ P) :=
      rfl

variable [deceqA : decidable_eq A]
include deceqA

-- find_lt_length can be used to generate a proof of Found if a ∈ l.
-- "kth (find a l) l Found" can be used to retrieve what is found. While that may seem
-- silly since we already have what we are looking for in "a",
-- "let elts := elems A, k := find b (map f elts) in kth k elts Found"
-- would allow us to use it as a map to reverse a finite function.

end kth

end list

-- less_than renamings (everything in namespace less_than) :
-- lt_dinj -> dinj_lt
-- lt_inv -> val_mk
-- updto_nodup -> nodup_upto
-- upto_complete -> mem_upto
-- upto_nil -> upto_zero
-- upto_map_eq_upto -> map_val_upto
-- upto_length -> length_upto
-- card_univ_lt_type -> card_less_than
