import OAI.Analysis.CircleDomains.Uniformization.ExteriorAnnulusCoefficients
import OAI.Analysis.CircleDomains.Sobolev.ExteriorAreaBoundProof
import OAI.Analysis.CircleDomains.Uniformization.ExteriorCoefficientBounds

namespace OAI

/-! The weighted Laurent square-sum follows from finite annular energy,
positive image-circle area and the principal normalization at infinity. -/
open Set Filter Function Metric Real MeasureTheory Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma finite_principal_coefficient_sum_le (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 1 < ‖z‖}) (hi : InjOn F {z | 1 < ‖z‖})
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹))
    {a : ℝ} (ha : 1 < a) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n : ℝ)+1)*‖principalLaurentCoefficient F n‖^2*
      (a⁻¹)^(2*(n+1))) ≤ a^2 := by
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop 1)] with z hz
    exact (hF z hz).differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  obtain ⟨c, T, hT, he⟩ := principal_exterior_expansion hd (principal_remainder_tendsto_zero hn)
  have hlim := principal_circle_area_limit hT he
  have hs : Tendsto (fun b : ℝ => ∑ n ∈ Finset.range N,
      ((n : ℝ)+1)*‖principalLaurentCoefficient F n‖^2*(b⁻¹)^(2*(n+1)))
      atTop (𝓝 0) := by
    have hterm (n : ℕ) : Tendsto (fun b : ℝ =>
        ((n : ℝ)+1)*‖principalLaurentCoefficient F n‖^2*(b⁻¹)^(2*(n+1)))
        atTop (𝓝 0) := by
      have hp : Tendsto (fun b : ℝ => (b⁻¹)^(2*(n+1))) atTop (𝓝 0) := by
        simpa using ((tendsto_inv_atTop_zero : Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 (0 : ℝ))).pow (2*(n+1)))
      simpa only [mul_zero] using hp.const_mul (((n : ℝ)+1)*‖principalLaurentCoefficient F n‖^2)
    simpa using tendsto_finsetSum (Finset.range N) (fun n _ => hterm n)
  have hle : ∀ᶠ b : ℝ in atTop,
      Real.pi*(∑ n ∈ Finset.range N, ((n : ℝ)+1)*‖principalLaurentCoefficient F n‖^2*
        (a⁻¹)^(2*(n+1))) ≤
      (signedCurveArea (fun t => F (unitCircleParam 0 b t))-Real.pi*b^2) +
        Real.pi*(∑ n ∈ Finset.range N, ((n : ℝ)+1)*‖principalLaurentCoefficient F n‖^2*
          (b⁻¹)^(2*(n+1))) + Real.pi*a^2 -
            signedCurveArea (fun t => F (unitCircleParam 0 a t)) := by
    filter_upwards [eventually_gt_atTop a] with b hab
    have hb := exterior_annulus_finite_coefficients (by norm_num) hF
      (principal_remainder_tendsto_zero hn) ha hab N
    rw [← exterior_annulus_area hgreen (by norm_num) hF ha hab] at hb
    simp_rw [mul_sub, Finset.sum_sub_distrib] at hb
    nlinarith
  have ht := ((hlim.add (hs.const_mul Real.pi)).add_const (Real.pi*a^2)).sub_const
    (signedCurveArea (fun t => F (unitCircleParam 0 a t)))
  have h := ge_of_tendsto ht hle
  have hpos := exterior_circle_area_pos hsch hgreen (by norm_num) hF hi hn ha
  simp only [mul_zero, add_zero, zero_add] at h
  nlinarith [Real.pi_pos]

lemma exteriorCoefficientAreaTheorem (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) : ExteriorCoefficientAreaTheorem := by
  intro F hF hi hn
  let c := principalLaurentCoefficient F
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, ((n : ℝ)+1)*‖c n‖^2) ≤ 1 := by
    have hs : ContinuousAt (fun a : ℝ => ∑ n ∈ Finset.range N,
        ((n : ℝ)+1)*‖c n‖^2*(a⁻¹)^(2*(n+1))) 1 := by
      apply tendsto_finsetSum
      intro n _
      exact continuousAt_const.mul (((continuousAt_id : ContinuousAt (fun a : ℝ => a) 1).inv₀
        (by norm_num)).pow (2*(n+1)))
    have ht : Tendsto (fun a : ℝ => ∑ n ∈ Finset.range N,
        ((n : ℝ)+1)*‖c n‖^2*(a⁻¹)^(2*(n+1))) (𝓝[>] 1)
        (𝓝 (∑ n ∈ Finset.range N, ((n : ℝ)+1)*‖c n‖^2)) := by
      simpa using hs.tendsto.mono_left nhdsWithin_le_nhds
    have ha : Tendsto (fun a : ℝ => a^2) (𝓝[>] 1) (𝓝 1) := by
      have h : Tendsto (fun a : ℝ => a^2) (𝓝[>] 1) (𝓝 ((1 : ℝ)^2)) :=
        ((continuousAt_id : ContinuousAt (fun a : ℝ => a) 1).pow 2).tendsto.mono_left
          nhdsWithin_le_nhds
      simpa only [one_pow] using h
    apply le_of_tendsto_of_tendsto ht ha
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact finite_principal_coefficient_sum_le hsch hgreen hF hi hn ha N
  have hnonneg (n : ℕ) : 0 ≤ ((n : ℝ)+1)*‖c n‖^2 := by positivity
  refine ⟨c, summable_of_sum_range_le hnonneg hb, Real.tsum_le_of_sum_range_le hnonneg hb, ?_⟩
  intro z hz
  have hu : AnalyticOnNhd ℂ (invertedPrincipalRemainder F) (ball 0 1) := by
    simpa using invertedPrincipalRemainder_analyticOnNhd (by norm_num : (0 : ℝ) < 1)
      hF (principal_remainder_tendsto_zero hn)
  exact principal_laurent_hasSum hu hz

end CircleDomainRigidity

end

end OAI
