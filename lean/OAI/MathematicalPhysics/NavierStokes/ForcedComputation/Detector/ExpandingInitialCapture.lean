import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneUnitImpulse
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneWeightedEvolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMovingCutoff
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneIntegralBounds

namespace OAI

/-! The injection is captured before the first moving stage.  Testing the
actual scalar equation gives the initial mass minus its diffusion loss. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows VelocityDetector Set MeasureTheory
open scoped ContDiff

theorem concentrationCutoff_mul_unitImpulse {R : ℝ} (hR : 1 ≤ R)
    (p : Plane) (t : ℝ) (x : Plane) :
    concentrationCutoff R p x * unitImpulse p t x = unitImpulse p t x := by
  by_cases hx : spatialImpulse p x = 0
  · simp [unitImpulse, hx]
  · have hs := spatialImpulse_support p hx
    have he : concentrationCutoff R p x = 1 := by
      apply concentrationCutoff_one (by linarith)
      intro j
      have hl := hs.1 j
      have hu := hs.2 j
      have hb : |x j - p j| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    rw [he, one_mul]

theorem initial_concentration_capture
    {T ν R C b : ℝ} {a : ℝ → Plane → Plane} {w : ℝ → Plane → ℝ}
    (p : Plane) (hw : PlaneScalarSolution T ν a (unitImpulse p) w)
    (hν : 0 ≤ ν) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C)
    (hwi : ∀ t ∈ Icc 0 T, Integrable (w t))
    (hwn : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ w t x)
    (hwm : ∀ t ∈ Icc 0 T, (∫ x, w t x) ≤ 1)
    (hb : 0 ≤ b) (hbT : b ≤ T)
    (haz : ∀ t ∈ Ioo 0 b, a t = fun _ => 0) :
    smoothRamp 0 1 b - ν * (R⁻¹ ^ 2 * C) * b ≤
      ∫ x, concentrationCutoff R p x * w b x := by
  let φ := concentrationCutoff R p
  let F : ℝ → ℝ := fun t => (∫ x, φ x * w t x) - smoothRamp 0 1 t
  let L := R⁻¹ ^ 2 * C
  have hL : 0 ≤ L := mul_nonneg (sq_nonneg _) hC
  have hφ := concentrationCutoff_smooth R p
  have hc := concentrationCutoff_compactSupport (by linarith : 0 < R) p
  have hcont : ContinuousOn F (Icc 0 b) :=
    ((hw.test_integral_continuousOn hφ hc).sub
      (smoothRamp_smooth 0 1).continuous.continuousOn).mono (Icc_subset_Icc le_rfl hbT)
  have hder (t : ℝ) (ht : t ∈ Ioo 0 b) :
      ∃ d, HasDerivAt F d t ∧ -(ν * L) ≤ d := by
    have htT : t ∈ Ioo 0 T := ⟨ht.1, ht.2.trans_le hbT⟩
    have hi := hw.test_integral_derivative ha (unitImpulse_smooth p) hdiv hφ hc htT
    have he : (∫ x, φ x * unitImpulse p t x) = smoothPulse 0 1 t := by
      simp_rw [show ∀ x, φ x * unitImpulse p t x = unitImpulse p t x from
        concentrationCutoff_mul_unitImpulse hR p t]
      exact unitImpulse_mass p t
    have hg : (∫ x, w t x * (ν * scalarLaplacian φ x + fderiv ℝ φ x (a t x))) =
        ν * ∫ x, w t x * scalarLaplacian φ x := by
      rw [haz t ht]
      simp only [ContinuousLinearMap.map_zero, add_zero]
      simp_rw [show ∀ x, w t x * (ν * scalarLaplacian φ x) =
        ν * (w t x * scalarLaplacian φ x) from fun x => by ring]
      exact integral_const_mul _ _
    rw [he, hg] at hi
    have hd := hi.sub ((smoothRamp_smooth 0 1).differentiable (by simp) t).hasDerivAt
    have hd' : HasDerivAt F (ν * ∫ x, w t x * scalarLaplacian φ x) t := by
      convert hd using 1
      simp [smoothPulse]
    refine ⟨_, hd', ?_⟩
    have hlap := concentrationCutoff_laplacian hΔ R p
    have heabs : (∫ x, |w t x|) = ∫ x, w t x := by
      congr 1
      funext x
      exact abs_of_nonneg (hwn t (Ioo_subset_Icc_self htT) x)
    have hiabs := abs_integral_mul_le (hwi t (Ioo_subset_Icc_self htT))
      (scalarLaplacian_smooth hφ).continuous.aestronglyMeasurable hlap
    rw [heabs] at hiabs
    have hiabs' : |∫ x, w t x * scalarLaplacian φ x| ≤ L :=
      hiabs.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hwm t (Ioo_subset_Icc_self htT)) hL)
    have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hiabs').1 hν
    nlinarith
  have hinc : F 0 - (ν * L) * (b - 0) ≤ F b := by
    apply lower_increment_of_derivative_bound hb hcont (d := deriv F)
    · intro t ht
      obtain ⟨d, hd, _⟩ := hder t ht
      rw [hd.deriv]
      exact hd
    · intro t ht
      obtain ⟨d, hd, hbound⟩ := hder t ht
      rw [hd.deriv]
      exact hbound
  have hzero : F 0 = 0 := by
    dsimp [F]
    rw [hw.initial]
    simp [smoothRamp_before (by norm_num : (0 : ℝ) < 1) le_rfl]
  rw [hzero] at hinc
  dsimp [F, L, φ] at hinc
  linarith

end ForcedComputation.ExpandingDetector

end

end OAI
