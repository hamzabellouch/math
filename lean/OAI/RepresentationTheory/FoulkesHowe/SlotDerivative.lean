import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SlotPolynomial

variable {R A S I B : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq S]

/-- Leibniz rule for a finite product, expressed by replacing one factor. -/
theorem derivation_prod (D : Derivation R A A) (s : Finset S) (f : S → A) :
    D (∏ i ∈ s, f i) =
      ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [Finset.prod_insert ha, Function.update_self, smul_eq_mul]
    have h₁ : (∏ j ∈ s, Function.update f a (D (f a)) j) = ∏ j ∈ s, f j :=
      Finset.prod_update_of_notMem ha _ _
    rw [h₁, Finset.mul_sum]
    have h₂ : (∑ i ∈ s, Function.update f i (D (f i)) a *
          ∏ j ∈ s, Function.update f i (D (f i)) j) =
        ∑ i ∈ s, f a * ∏ j ∈ s, Function.update f i (D (f i)) j := by
      apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := by
        intro h
        subst i
        exact ha hi
      rw [Function.update_of_ne hai]
    rw [h₂]
    ring

variable [Fintype S] [Fintype I]

/-- Coordinate polynomial of a coefficient array and an assignment of slots to blocks. -/
def polynomial (c : (S → I) → R) (l : S → B) : MvPolynomial (B × I) R :=
  ∑ k : S → I, MvPolynomial.C (c k) * ∏ s : S, MvPolynomial.X (l s, k s)

/-- A directional block derivation replaces each occurrence of the source block in turn. -/
theorem derivation_polynomial [DecidableEq B]
    (c : (S → I) → R) (l : S → B) (src dst : B)
    (D : Derivation R (MvPolynomial (B × I) R) (MvPolynomial (B × I) R))
    (hD : ∀ b i, D (MvPolynomial.X (b, i)) =
      if b = src then MvPolynomial.X (dst, i) else 0) :
    D (polynomial c l) =
      ∑ s ∈ Finset.univ.filter (fun s => l s = src),
        polynomial c (Function.update l s dst) := by
  classical
  unfold polynomial
  rw [map_sum]
  simp_rw [D.leibniz, MvPolynomial.derivation_C, smul_zero, add_zero,
    smul_eq_mul, derivation_prod]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : l s = src
  · simp only [h, ite_true]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hjs : j = s
    · subst j
      simp [hD]
    · simp [Function.update_of_ne hjs]
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro k hk
    have hz : (∏ j : S, Function.update (fun s => MvPolynomial.X (l s, k s))
        s (D (MvPolynomial.X (l s, k s))) j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ s)
      simp [hD, h]
    rw [hz, mul_zero]

/-- Reindexing slots moves the same permutation onto the coefficient array. -/
theorem polynomial_reindex (c : (S → I) → R) (l : S → B) (e : Equiv.Perm S) :
    polynomial c (l ∘ e) = polynomial (fun k => c (k ∘ e)) l := by
  classical
  unfold polynomial
  apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl I))
  intro k
  congr 1
  · congr 1
    change c k = c _
    congr 1
    funext s
    simp
  · apply Fintype.prod_equiv e
    intro s
    simp

/-- Symmetry of coefficients induces invariance under the same permutation of slot labels. -/
theorem polynomial_reindex_of_invariant (c : (S → I) → R) (l : S → B)
    (e : Equiv.Perm S) (hc : ∀ k, c (k ∘ e) = c k) :
    polynomial c (l ∘ e) = polynomial c l := by
  rw [polynomial_reindex]
  congr 1
  funext k
  exact hc k

/-- Swapping two equal-labelled slots shows that replacing either label gives the same polynomial. -/
theorem polynomial_update_eq (c : (S → I) → R) (l : S → B) (s t : S) (dst : B)
    (hl : l s = l t)
    (hc : ∀ k, c (k ∘ Equiv.swap s t) = c k) :
    polynomial c (Function.update l s dst) = polynomial c (Function.update l t dst) := by
  classical
  have hlabels : Function.update l s dst =
      Function.update l t dst ∘ Equiv.swap s t := by
    funext j
    by_cases hjs : j = s
    · subst j
      simp
    by_cases hjt : j = t
    · subst j
      simp [hjs, Ne.symm hjs, hl]
    · simp [Equiv.swap_apply_of_ne_of_ne hjs hjt, hjs, hjt]
  rw [hlabels]
  exact polynomial_reindex_of_invariant c _ _ hc

/-- If all source-labelled slots are interchangeable, the derivative is a single replacement
multiplied by their number. -/
theorem derivation_polynomial_eq_card_smul [DecidableEq B]
    (c : (S → I) → R) (l : S → B) (src dst : B) (t : S) (ht : l t = src)
    (D : Derivation R (MvPolynomial (B × I) R) (MvPolynomial (B × I) R))
    (hD : ∀ b i, D (MvPolynomial.X (b, i)) =
      if b = src then MvPolynomial.X (dst, i) else 0)
    (hc : ∀ s, l s = src → ∀ k, c (k ∘ Equiv.swap s t) = c k) :
    D (polynomial c l) =
      (Finset.univ.filter (fun s => l s = src)).card •
        polynomial c (Function.update l t dst) := by
  classical
  rw [derivation_polynomial c l src dst D hD, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := (Finset.mem_filter.mp hs).2
  exact polynomial_update_eq c l s t dst (hs'.trans ht.symm) (hc s hs')

end Problem346.SlotPolynomial

end

end OAI
