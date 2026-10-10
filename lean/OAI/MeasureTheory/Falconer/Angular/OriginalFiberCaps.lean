import OAI.MeasureTheory.Falconer.Estimates.DescriptorFiberBad
import OAI.MeasureTheory.Falconer.Angular.SphereCapCenters
import OAI.MeasureTheory.Falconer.Estimates.Availability
import OAI.MeasureTheory.Falconer.Radial.RadialSphereBounds

namespace OAI

/-! # The prepared radial cap bound controls each original sphere law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem eventual_original_fiber_caps {σ s : ℝ} (hσ : 0 < σ) (hs : 0 ≤ s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ μ ν : ProbabilityMeasure (Space d), ∀ G : Set (Space d × Space d),
      (∀ x ∈ (μ : Measure (Space d)).support, ∀ y, (x,y) ∈ G → y ≠ x) →
      (∀ x ∈ (μ : Measure (Space d)).support, ∀ w : Space d, ‖w‖ = 1 →
        ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        (ν : Measure (Space d)) {y | (x,y) ∈ G ∧ dist (radialDirection x y) w < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(σ/2)*r^s)) →
      ∀ w₀ : Sphere d, ∀ x ∈ (μ : Measure (Space d)).support,
      ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^s) := by
  obtain ⟨N₀,h₀⟩ := Regularization.fixed_constant_absorbed (half_pos hσ) ((2:ℝ)^s)
  refine ⟨N₀,?_⟩
  intro N hN μ ν G hdiag hcap w₀ x hx u r hr hr1
  let R : ℝ := (2:ℝ)^N
  let V := originalRadialSphereLaw w₀ ν G x
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hL : 1 ≤ R^(σ/2) := Real.one_le_rpow hR (half_pos hσ).le
  have hmass : V univ ≤ 1 := (originalRadialSphereLaw_mass_le w₀ ν G x).trans (by simp)
  have hball (w : Sphere d) (t : ℝ) (ht : R⁻¹ ≤ t) (ht1 : t ≤ 1) :
      V (Metric.ball w t) ≤ ENNReal.ofReal (R^(σ/2)*t^s) := by
    rw [originalRadialSphereLaw_ball w₀ ν G x (hdiag x hx)]
    simpa only [radialDirection,NormedSpace.normalize] using hcap x hx w (sphere_norm w) t ht ht1
  have hb := sphere_cap_arbitrary_center V hR hL hs hmass hball u
    (by simpa only [R,Real.rpow_neg_one] using hr) hr1
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hc := h₀ N hN
  have he : R^(σ/2)*R^(σ/2) = R^σ := by
    rw [← Real.rpow_add (by dsimp [R]; positivity)]
    congr 1
    ring
  calc
    _ ≤ (R^(σ/2)*R^(σ/2))*r^s := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
        (Real.rpow_nonneg (le_trans (by positivity : 0 ≤ R^(-1:ℝ)) hr) _)
    _ = _ := by rw [he]

end Falconer

end OAI
