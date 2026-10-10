import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedWindow

namespace OAI

/-! # One Y prior and both H priors in the actual matched correlation -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def retainedPairAssignmentEquiv (H Y A : Type*) :
    ((Y → A) × (H → A)) ≃ (H ⊕ Y → A) where
  toFun a := Sum.elim a.2 a.1
  invFun x := ((fun y => x (.inr y)), (fun h => x (.inl h)))
  left_inv _ := rfl
  right_inv x := by funext i; cases i <;> rfl

theorem finite_matched_prior_fubini {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (e : Equiv.Perm H)
    (F : (H ⊕ Y → P) → ℂ) :
    (∑ x : H ⊕ Y → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) * F x) =
    ∑ u : Y → P, ((∏ y, primeSubsetPrior P (Q (.inr y)) (u y) : ℝ) : ℂ) *
      ∑ l : H → P, ((∏ h, primeSubsetPrior P (Q (.inl h)) (l h) : ℝ) : ℂ) *
        ((∏ h, primeSubsetPrior P (Q (.inl h)) (l (e h)) : ℝ) : ℂ) * F (Sum.elim l u) := by
  rw [← (retainedPairAssignmentEquiv H Y P).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change ((∏ i, primeSubsetPrior P (Q i) (Sum.elim l u i) : ℝ) : ℂ) *
    ((∏ h, primeSubsetPrior P (Q (.inl h)) (l (e h)) : ℝ) : ℂ) * F (Sum.elim l u) = _
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Complex.ofReal_mul]
  ring

end Ostmann

end OAI
