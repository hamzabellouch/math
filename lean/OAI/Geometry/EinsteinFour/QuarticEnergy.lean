import OAI.Geometry.EinsteinFour.Energy
import OAI.Geometry.EinsteinFour.Quartic

namespace OAI

/-! The full scalar quartic estimate, with both energy and spectral defects. -/

namespace PositiveEinsteinFour.QuarticEnergy

open Energy Quartic

noncomputable section

/-- The coefficient `g` in the weighted Hessian projection bound. -/
def projectionCoefficient (v y σ ρ : ℝ) : ℝ :=
  (7 / 12) * (4 + y) - σ * v + ρ ^ 2 * v ^ 2 / 4

/-- The normalized spectral parameter controls the actual projection cost. -/
theorem projectionCoefficient_le
    {v b r σ ρ W : ℝ}
    (hv : 0 ≤ v) (hr : 1 ≤ r) (hr2 : r ≤ 2) (hvr : v * r ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2) :
    projectionCoefficient v (b + W) σ ρ ≤ projectionBound v b (v * r - v) W := by
  have h := spectral_defect_bound hv hr hr2 hvr hσ hρ
  unfold projectionCoefficient projectionBound
  linarith

/-- At zero energy defects the expression in (19) is exactly the scalar form
bounded by the homogeneous inequality (20). -/
theorem energy_zero_defect_identity
    (v b V W H Hb P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    quarticEnergy v b (P ^ 2) (Q ^ 2)
      (projectionBound v b V W) (projectionBound b v W V) H Hb (P ^ 2) (Q ^ 2) =
    (3 / 10) * (P + Q) *
      ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3) +
    (27 / 320) * (P + Q) ^ 2 *
      (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) -
    (2 / 5) * (17 / 10) * (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) := by
  have hk : (Real.sqrt (3 / 5 : ℝ)) ^ 2 = (3 / 5 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold quarticEnergy gradientSum scalarWeight
  rw [Real.sqrt_sq hP, Real.sqrt_sq hQ]
  ring_nf
  rw [hk]
  ring

/-- Increasing the fixed radial coefficients increases the zero-defect
energy expression. The remaining coefficients are irrelevant at zero defect. -/
theorem energy_zero_defect_mono_coefficients
    (v b H Hb P Q g gb g' gb' : ℝ) (hg : g ≤ g') (hgb : gb ≤ gb') :
    quarticEnergy v b (P ^ 2) (Q ^ 2) g gb H Hb (P ^ 2) (Q ^ 2) ≤
      quarticEnergy v b (P ^ 2) (Q ^ 2) g' gb' H Hb (P ^ 2) (Q ^ 2) := by
  have hc : 0 ≤ (9 / 64 : ℝ) * (gradientSum (P ^ 2) (Q ^ 2)) ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hg (sq_nonneg P))
      (mul_le_mul_of_nonneg_right hgb (sq_nonneg Q))) hc
  unfold quarticEnergy
  simp only [sub_self, mul_zero, add_zero]
  linarith

/-- The entire right side of equation (19) is bounded by the negative quartic
term, retaining the actual spectral coefficients and arbitrary nonnegative
energy defects. The normalized eigenvalue parameters supply the spectral
restrictions rather than assuming axial curvature. -/
theorem quartic_energy_bound
    {v b r s σ τ ρ χ P Q e f : ℝ}
    (hv : 0 < v) (hb : 0 < b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (he : P ^ 2 ≤ e) (hf : Q ^ 2 ≤ f) :
    quarticEnergy v b (P ^ 2) (Q ^ 2)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f ≤
    -(2 / 5 - 3 * v * b / 10) * (9 / 25) *
      (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) := by
  have hvx : v ≤ v * r := by nlinarith
  have hby : b ≤ b * s := by nlinarith
  have hV : 0 ≤ v * r - v := by linarith
  have hW : 0 ≤ b * s - b := by linarith
  have hsum : (v * r - v) + (b * s - b) ≤ 2 - v - b := by linarith
  have hg := projectionCoefficient_le (b := b) (W := b * s - b)
    hv.le hr hr2 (by nlinarith) hσ hρ
  have hgb := projectionCoefficient_le (b := v) (W := v * r - v)
    hb.le hs hs2 (by nlinarith) hτ hχ
  rw [show b + (b * s - b) = b * s by ring] at hg
  rw [show v + (v * r - v) = v * r by ring] at hgb
  calc
    _ ≤ quarticEnergy v b (P ^ 2) (Q ^ 2)
        (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
        (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) (P ^ 2) (Q ^ 2) :=
      remove_energy_defects_from_spectral_bounds _ _ hv hb hvx hby hspectral
        (sq_nonneg P) (sq_nonneg Q) he hf
    _ ≤ quarticEnergy v b (P ^ 2) (Q ^ 2)
        (projectionBound v b (v * r - v) (b * s - b))
        (projectionBound b v (b * s - b) (v * r - v))
        (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) (P ^ 2) (Q ^ 2) :=
      energy_zero_defect_mono_coefficients _ _ _ _ _ _ _ _ _ _ hg hgb
    _ = _ := energy_zero_defect_identity _ _ _ _ _ _ _ _ hP hQ
    _ ≤ _ := zero_defect_quartic_bound hv hb hV hW hsum hP hQ

/-- The same estimate in the squared gradient variables of the combined
integrand: `a = |p|²` and `d = |q|²`. -/
theorem quartic_energy_bound_gradient
    {v b r s σ τ ρ χ a d e f : ℝ}
    (hv : 0 < v) (hb : 0 < b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (he : (5 / 3) * a ≤ e) (hf : (5 / 3) * d ≤ f) :
    quarticEnergy v b ((5 / 3) * a) ((5 / 3) * d)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f ≤
      -(2 / 5 - 3 * v * b / 10) * (a + d) * (a / v + d / b) := by
  have hP : 0 ≤ (5 / 3 : ℝ) * a := by positivity
  have hQ : 0 ≤ (5 / 3 : ℝ) * d := by positivity
  have h := quartic_energy_bound (e := e) (f := f) hv hb hr hr2 hs hs2 hspectral hσ hρ hτ hχ
    (Real.sqrt_nonneg ((5 / 3) * a)) (Real.sqrt_nonneg ((5 / 3) * d))
    (by rwa [Real.sq_sqrt hP]) (by rwa [Real.sq_sqrt hQ])
  rw [Real.sq_sqrt hP, Real.sq_sqrt hQ] at h
  calc
    _ ≤ -(2 / 5 - 3 * v * b / 10) * (9 / 25) *
        ((5 / 3) * a + (5 / 3) * d) * (((5 / 3) * a) / v + ((5 / 3) * d) / b) := h
    _ = _ := by ring

end
end PositiveEinsteinFour.QuarticEnergy

end OAI
