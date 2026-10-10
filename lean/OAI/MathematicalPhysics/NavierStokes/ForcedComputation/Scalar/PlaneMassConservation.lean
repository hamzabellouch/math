import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneWeightedEvolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneMassContinuity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCutoffCoefficients
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCutoffLimit
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneIntegralBounds

namespace OAI

/-! Mass conservation is derived from compact tests and vanishing
inverse-square diffusion errors. It is not a hypothesis in the scalar
existence input. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows ExpandingDetector Set MeasureTheory Filter
open scoped ContDiff Topology

theorem PlaneScalarSolution.mass_eq_source
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x)
    {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc 0 T)) (hθ0 : θ 0 = 0)
    (hθd : ∀ t ∈ Ioo 0 T, HasDerivAt θ (∫ x, h t x) t) :
    (∫ x, w T x) = θ T := by
  obtain ⟨B, hB, hwb⟩ := hw.uniform_tail_bound hT hν ha hh hc hpos
  have hwi := hw.integrable hT hν ha hh hc hpos
  let M : ℝ := ∫ x, B * planeTailProfile x
  have hmass (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ x, |w t x|) ≤ M := by
    apply integral_mono (hwi t ht).norm (planeTailProfile_integrable.const_mul B)
    intro x
    simpa only [Real.norm_eq_abs] using hwb t ht x
  obtain ⟨C, hC, hΔ⟩ := massCutoff_laplacian_bound
  obtain ⟨N, hN⟩ := hc.cutoff_eventually_exact T hT
  let φ : ℕ → Plane → ℝ := fun n => concentrationCutoff ((n : ℝ) + 1) 0
  let E : ℕ → ℝ := fun n => ν * (((n : ℝ) + 1)⁻¹ ^ 2 * C) * M * T
  have herror (n : ℕ) (hn : N ≤ n) : |(∫ x, φ n x * w T x) - θ T| ≤ E n := by
    have hφ : ContDiff ℝ ∞ (φ n) := concentrationCutoff_smooth _ _
    have hφc : HasCompactSupport (φ n) := concentrationCutoff_compactSupport (by positivity) _
    have hscale : 0 ≤ ((n : ℝ) + 1)⁻¹ ^ 2 * C := by positivity
    have hD (s : ℝ) (hs : s ∈ Ioo 0 T) :
        HasDerivAt (fun r => (∫ x, φ n x * w r x) - θ r)
          (ν * ∫ x, w s x * scalarLaplacian (φ n) x) s := by
      have htest := (hw.test_integral_derivative ha hh hdiv hφ hφc hs).sub (hθd s hs)
      have hid :
          ((∫ x, w s x * (ν * scalarLaplacian (φ n) x + fderiv ℝ (φ n) x (a s x))) +
            ∫ x, φ n x * h s x) - (∫ x, h s x) =
          ν * ∫ x, w s x * scalarLaplacian (φ n) x := by
        have he (x : Plane) : w s x * (ν * scalarLaplacian (φ n) x +
            fderiv ℝ (φ n) x (a s x)) = ν * (w s x * scalarLaplacian (φ n) x) := by
          rw [(hN n hn s (Ioo_subset_Icc_self hs) x).1]
          ring
        have hh' (x : Plane) : φ n x * h s x = h s x :=
          (hN n hn s (Ioo_subset_Icc_self hs) x).2
        simp_rw [he, hh']
        rw [integral_const_mul]
        ring
      rw [hid] at htest
      exact htest
    have hbound (s : ℝ) (hs : s ∈ Ioo 0 T) :
        |ν * ∫ x, w s x * scalarLaplacian (φ n) x| ≤
          ν * (((n : ℝ) + 1)⁻¹ ^ 2 * C) * M := by
      have hsc : AEStronglyMeasurable (scalarLaplacian (φ n)) volume :=
        (scalarLaplacian_smooth hφ).continuous.aestronglyMeasurable
      have hi := abs_integral_mul_le (hwi s (Ioo_subset_Icc_self hs)) hsc
        (concentrationCutoff_laplacian (fun x => hΔ x) ((n : ℝ) + 1) 0)
      rw [abs_mul, abs_of_nonneg hν]
      calc
        _ ≤ ν * ((((n : ℝ) + 1)⁻¹ ^ 2 * C) * ∫ x, |w s x|) :=
          mul_le_mul_of_nonneg_left hi hν
        _ ≤ ν * ((((n : ℝ) + 1)⁻¹ ^ 2 * C) * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hmass s (Ioo_subset_Icc_self hs)) hscale) hν
        _ = _ := by ring
    have hi := abs_increment_le_of_derivative_bound hT
      ((hw.test_integral_continuousOn hφ hφc).sub hθ) hD hbound
    have hz : (∫ x, φ n x * w 0 x) - θ 0 = 0 := by
      simp only [hw.initial, mul_zero, integral_zero, hθ0, sub_self]
    simpa only [Pi.sub_apply, hz, sub_zero, E] using hi
  have hlim : Tendsto (fun n : ℕ => |(∫ x, φ n x * w T x) - θ T|)
      atTop (𝓝 |(∫ x, w T x) - θ T|) :=
    ((concentrationCutoff_integral_limit (hwi T ⟨hT, le_rfl⟩) 0).sub_const (θ T)).abs
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have he : Tendsto E atTop (𝓝 0) := by
    simpa only [E, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero] using
      ((((hr.pow 2).mul_const (C : ℝ)).const_mul ν).mul_const M).mul_const T
  have hz : |(∫ x, w T x) - θ T| ≤ 0 :=
    le_of_tendsto_of_tendsto hlim he ((eventually_ge_atTop N).mono (fun n hn => herror n hn))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

end ForcedComputation.VelocityDetector

end

end OAI
