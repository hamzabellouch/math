import OAI.Geometry.RCD.Metric.LocalDensityOrder
import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests
import OAI.Geometry.RCD.Sobolev.SupportedEnergyLocality
import OAI.Geometry.RCD.Sobolev.ContinuousSobolevPairingBound

namespace OAI

/-! # Local uniqueness of L2 weak Laplacians

Compact Lipschitz tests determine the source on each interior region.
The functions and their sources need only agree on the working set.
-/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] (μ : Measure X)
  [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem IsWeakLaplacian.local_source_eq {Ω S : Set X} (hΩ : IsCompact Ω)
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    {u v : SobolevSpace μ Q} {d e : Lp ℝ 2 μ}
    (hd : IsWeakLaplacian μ Q u d) (he : IsWeakLaplacian μ Q v e)
    (huv : SobolevSpace.toLp μ Q u =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q v)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0 ≤ χ) (hχ1 : ∀ x ∈ S, χ x = 1) :
    d =ᵐ[μ.restrict S] e := by
  have htest (q : compactLipschitzTests Ω) :
      (∫ x, (q : X →ᵇ ℝ) x*(d x-e x) ∂μ) = 0 := by
    let ψ := compactTestSobolev μ Q Ω q
    have hψ := compactTestSobolev_coe μ Q Ω q
    change SobolevSpace.toLp μ Q ψ =ᵐ[μ] (q : X →ᵇ ℝ) at hψ
    have hE := energyForm_eq_of_test_support μ Q hΩ.measurableSet huv q hψ
      q.property.choose_spec.2.2
    have hId : inner ℝ d (SobolevSpace.toLp μ Q ψ) =
        ∫ x, (q : X →ᵇ ℝ) x*d x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ] with x hx
      simp only [Real.inner_apply,hx]
      ring
    have hIe : inner ℝ e (SobolevSpace.toLp μ Q ψ) =
        ∫ x, (q : X →ᵇ ℝ) x*e x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ] with x hx
      simp only [Real.inner_apply,hx]
      ring
    have hdi := (Lp.memLp (SobolevSpace.toLp μ Q ψ)).integrable_mul (Lp.memLp d)
    have hei := (Lp.memLp (SobolevSpace.toLp μ Q ψ)).integrable_mul (Lp.memLp e)
    have hdi' : Integrable (fun x => (q : X →ᵇ ℝ) x*d x) μ := by
      apply hdi.congr
      filter_upwards [hψ] with x hx
      exact congrArg (fun a => a*d x) hx
    have hei' : Integrable (fun x => (q : X →ᵇ ℝ) x*e x) μ := by
      apply hei.congr
      filter_upwards [hψ] with x hx
      exact congrArg (fun a => a*e x) hx
    have hh : (fun x => (q : X →ᵇ ℝ) x*(d x-e x)) =
        (fun x => (q : X →ᵇ ℝ) x*d x-(q : X →ᵇ ℝ) x*e x) := by
      funext x
      ring
    rw [hh,integral_sub hdi' hei']
    rw [hd ψ,he ψ,hId,hIe] at hE
    linarith only [hE]
  have hi : IntegrableOn (fun x => d x-e x) Ω μ :=
    (lp_integrableOn_of_finite μ d Ω hΩ.measure_lt_top.ne).sub
      (lp_integrableOn_of_finite μ e Ω hΩ.measure_lt_top.ne)
  have hpos := local_density_nonneg_of_tests_integrableOn μ hΩ.measurableSet hi
    hS hSΩ χ hχ hχc hχΩ hχ0 hχ1 (fun q _ => (htest q).ge)
  have hneg := local_density_nonneg_of_tests_integrableOn μ hΩ.measurableSet hi.neg
    hS hSΩ χ hχ hχc hχΩ hχ0 hχ1 (fun q _ => by
      have hh : (fun x => (q : X →ᵇ ℝ) x* -(d x-e x)) =
          -(fun x => (q : X →ᵇ ℝ) x*(d x-e x)) := by
        funext x
        change (q : X →ᵇ ℝ) x* -(d x-e x) = -((q : X →ᵇ ℝ) x*(d x-e x))
        ring
      change 0 ≤ ∫ x, (q : X →ᵇ ℝ) x* -(d x-e x) ∂μ
      rw [hh]
      change 0 ≤ ∫ x, -((q : X →ᵇ ℝ) x*(d x-e x)) ∂μ
      rw [integral_neg,htest q,neg_zero])
  filter_upwards [hpos,hneg] with x hp hn
  change 0 ≤ -(d x-e x) at hn
  linarith only [hp,hn]

end RegularPointCoordinates

end

end OAI
