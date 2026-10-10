import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- For a positively homogeneous support bound, unit directions determine all
directions. This connects the unit-sphere definition with an
explicit zonotope's halfspace description. -/
theorem unit_support_halfspaces_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (hzero : 0 ≤ f 0)
    (hscale : ∀ (a : ℝ), 0 ≤ a → ∀ u, f (a • u) = a * f u) :
    {x : V | ∀ u, ‖u‖ = 1 → ⟪u, x⟫ ≤ f u} =
      {x : V | ∀ u, ⟪u, x⟫ ≤ f u} := by
  ext x
  constructor
  · intro hx u
    by_cases hu : u = 0
    · simpa [hu] using hzero
    have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    let v : V := ‖u‖⁻¹ • u
    have hv : ‖v‖ = 1 := by
      simp [v, norm_smul, hnorm]
    have huv : ‖u‖ • v = u := by
      simp [v, smul_smul, hnorm]
    calc
      ⟪u, x⟫ = ‖u‖ * ⟪v, x⟫ := by
        rw [← real_inner_smul_left, huv]
      _ ≤ ‖u‖ * f v := mul_le_mul_of_nonneg_left (hx v hv) (norm_nonneg u)
      _ = f u := by rw [← hscale ‖u‖ (norm_nonneg u) v, huv]
  · intro hx u _
    exact hx u

end ProjectionCounterexample

end

end OAI
