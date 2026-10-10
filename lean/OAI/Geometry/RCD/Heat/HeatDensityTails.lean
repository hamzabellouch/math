import OAI.Geometry.RCD.Heat.HeatPointwiseDecay
import OAI.Geometry.RCD.Heat.HeatDensityL2

namespace OAI

/-! # Gaussian L² tails for every heat-density row -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonDensity_L2_tail (t : ℝ) (ht : 0 < t) :
    ∃ r C : ℝ, 0 < r ∧ 1 ≤ C ∧ ∀ (x : X) (D : ℝ), r ≤ D →
      (∫ y in {y | D ≤ dist x y}, (hX.heatRadonDensity hn p t ht x y)^2 ∂hausdorff n X) ≤
        (C/Real.sqrt ((hausdorff n X).real (ball x r))*Real.exp (-(D-r)^2/(4*t)))^2 := by
  obtain ⟨r,hr,hrt,hcurv⟩ := exists_heat_local_radius K t ht
  obtain ⟨C,hC,hpoint⟩ := hX.boundedHeat_offDiagonal_evaluation hn p
  refine ⟨r,C,hr,hC,?_⟩
  intro x D hrD
  let μ := hausdorff n X
  let ρ := hX.heatRadonDensity hn p t ht x
  let S := {y | D ≤ dist x y}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  let A := C/Real.sqrt (μ.real (ball x r))*Real.exp (-(D-r)^2/(4*t))
  have hAn : 0 ≤ A := mul_nonneg (div_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  have hfull := integral_sq_le_of_capped_pairing (μ.restrict S)
    (hX.heatRadonDensity_measurable hn p t ht x)
    (hX.heatRadonDensity_integrable hn p t ht x).integrableOn
    (hX.heatRadonDensity_nonneg hn p t ht x) hAn
  apply (hfull ?_).2
  intro B
  let v := fun y => min (ρ y) B
  have hi : Integrable v μ := integrable_min_nonneg μ
    (hX.heatRadonDensity_integrable hn p t ht x) (hX.heatRadonDensity_nonneg hn p t ht x) B
  have hisq : Integrable (fun y => (v y)^2) μ := by
    simpa only [v,pow_two] using integrable_capped_product μ
      (hX.heatRadonDensity_integrable hn p t ht x) (hX.heatRadonDensity_integrable hn p t ht x)
      (hX.heatRadonDensity_nonneg hn p t ht x) (hX.heatRadonDensity_nonneg hn p t ht x) B
  have hv : MemLp v 2 μ := (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr hisq
  have hw := hv.indicator hS
  let g := hw.toLp (S.indicator v)
  have hg : ∀ᵐ y ∂μ, |g y| ≤ B := by
    filter_upwards [hw.coeFn_toLp] with y hy
    rw [hy]
    by_cases hs : y ∈ S
    · rw [indicator_of_mem hs,abs_of_nonneg (le_min (hX.heatRadonDensity_nonneg hn p t ht x y) B.coe_nonneg)]
      exact min_le_right _ _
    · rw [indicator_of_notMem hs,abs_zero]
      exact B.coe_nonneg
  have hfar : ∀ᵐ y ∂μ, g y ≠ 0 → D ≤ dist x y := by
    filter_upwards [hw.coeFn_toLp] with y hy hne
    by_contra hh
    have hs : y ∉ S := hh
    exact hne (hy.trans (indicator_of_notMem hs v))
  have hrep := hX.heatRadonDensity_integral_bounded hn p t ht x g B hg
  have he : (∫ y in S, ρ y*v y ∂μ) = ∫ y, ρ y*g y ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with y hy
    rw [hy]
    change S.indicator (fun y => ρ y*v y) y = ρ y*S.indicator v y
    by_cases hs : y ∈ S
    · simp only [indicator_of_mem hs]
    · simp only [indicator_of_notMem hs,mul_zero]
  have hnrm : ‖g‖ = Real.sqrt (∫ y in S, (v y)^2 ∂μ) := by
    have heq : (∫ y in S, (v y)^2 ∂μ) = ‖g‖^2 := by
      rw [← integral_sq_Lp μ g,← integral_indicator hS]
      apply integral_congr_ae
      filter_upwards [hw.coeFn_toLp] with y hy
      rw [hy]
      by_cases hs : y ∈ S <;> simp only [indicator_of_mem,indicator_of_notMem,hs,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
    rw [heq,Real.sqrt_sq (norm_nonneg g)]
  calc
    _ = ∫ y, ρ y*g y ∂μ := he
    _ = hX.boundedHeat hn p g ⟨B,hg⟩ t ht x := hrep
    _ ≤ |hX.boundedHeat hn p g ⟨B,hg⟩ t ht x| := le_abs_self _
    _ ≤ C/Real.sqrt (μ.real (ball x r))*(Real.exp (-(D-r)^2/(4*t))*‖g‖) :=
      hpoint x r t D ht hr hcurv hrt hrD g ⟨B,hg⟩ hfar
    _ = _ := by rw [hnrm]; exact (mul_assoc _ _ _).symm

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
