import OAI.Geometry.RCD.Heat.GaussianScaleAbsorption

namespace OAI

/-! # Absorbing the gradient singularity at a separated annulus -/

noncomputable section
namespace RegularPointCoordinates

/-- After the ball-volume power is included, separation by half the working
radius absorbs the full short-time gradient singularity. -/
theorem exists_annular_gaussian_gradient_bound (n : ℕ) {D : ℝ} (hD : 0 < D) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ R t : ℝ, 0 < R → 0 < t → t ≤ R^2 →
      ((R/Real.sqrt t)^n/Real.sqrt t)*Real.exp (-(R/2)^2/(D*t)) ≤ Q/R := by
  obtain ⟨Q,hQ,hb⟩ := exists_gaussian_polynomial_bound (n+1)
    (by positivity : 0 < (4*D)⁻¹)
  refine ⟨Q,hQ,?_⟩
  intro R t hR ht htR
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : (Real.sqrt t)^2 = t := Real.sq_sqrt ht.le
  have hu : 1 ≤ R/Real.sqrt t := (le_div_iff₀ hs).mpr (by nlinarith [Real.sqrt_nonneg t])
  have he : -((4*D)⁻¹)*(R/Real.sqrt t)^2 = -(R/2)^2/(D*t) := by
    rw [div_pow,hs2]
    field_simp
    ring
  have hp : (R/Real.sqrt t)^(n+1)/R = (R/Real.sqrt t)^n/Real.sqrt t := by
    rw [pow_succ]
    field_simp
  have hh := div_le_div_of_nonneg_right (hb (R/Real.sqrt t) hu) hR.le
  rw [he] at hh
  calc
    _ = ((R/Real.sqrt t)^(n+1)/R)*Real.exp (-(R/2)^2/(D*t)) := by rw [hp]
    _ = ((R/Real.sqrt t)^(n+1)*Real.exp (-(R/2)^2/(D*t)))/R := by ring
    _ ≤ _ := hh

end RegularPointCoordinates

end

end OAI
