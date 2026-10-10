import OAI.Geometry.RCD.Heat.HeatPointEvaluation
import OAI.Geometry.RCD.Harmonic.CappedPairingL2

namespace OAI

/-! # L² heat densities without a Gaussian input

The pointwise heat evaluation estimate is tested against capped versions
of its actual Radon--Nikodym density. Monotone convergence gives the
square-integrable row and its volume-normalized bound.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonDensity_square_bound (t : ℝ) (ht : 0 < t) :
    ∃ R C : ℝ, 0 < R ∧ 1 ≤ C ∧ ∀ x : X,
      Integrable (fun y => (hX.heatRadonDensity hn p t ht x y)^2) (hausdorff n X) ∧
      (∫ y, (hX.heatRadonDensity hn p t ht x y)^2 ∂hausdorff n X) ≤
        (C/Real.sqrt ((hausdorff n X).real (ball x R)))^2 := by
  obtain ⟨R,C,hR,hC,heval⟩ := hX.boundedHeat_L2_evaluation hn p t ht
  refine ⟨R,C,hR,hC,?_⟩
  intro x
  let μ := hausdorff n X
  let ρ := hX.heatRadonDensity hn p t ht x
  let A := C/Real.sqrt (μ.real (ball x R))
  have hAn : 0 ≤ A := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  apply integral_sq_le_of_capped_pairing μ (hX.heatRadonDensity_measurable hn p t ht x)
    (hX.heatRadonDensity_integrable hn p t ht x) (hX.heatRadonDensity_nonneg hn p t ht x) hAn
  intro D
  let v := fun y => min (ρ y) D
  have hi : Integrable v μ := integrable_min_nonneg μ
    (hX.heatRadonDensity_integrable hn p t ht x) (hX.heatRadonDensity_nonneg hn p t ht x) D
  have hisq : Integrable (fun y => (v y)^2) μ := by
    simpa only [v,pow_two] using integrable_capped_product μ
      (hX.heatRadonDensity_integrable hn p t ht x) (hX.heatRadonDensity_integrable hn p t ht x)
      (hX.heatRadonDensity_nonneg hn p t ht x) (hX.heatRadonDensity_nonneg hn p t ht x) D
  have hv : MemLp v 2 μ := (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr hisq
  let g := hv.toLp v
  have hg : ∀ᵐ y ∂μ, |g y| ≤ D := by
    filter_upwards [hv.coeFn_toLp] with y hy
    rw [hy,abs_of_nonneg (le_min (hX.heatRadonDensity_nonneg hn p t ht x y) D.coe_nonneg)]
    exact min_le_right _ _
  have hrep := hX.heatRadonDensity_integral_bounded hn p t ht x g D hg
  have he : (∫ y, ρ y * v y ∂μ) = ∫ y, ρ y * g y ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with y hy
    rw [hy]
  have hnrm : ‖g‖ = Real.sqrt (∫ y, (v y)^2 ∂μ) := by
    have heq : (∫ y, (v y)^2 ∂μ) = ‖g‖^2 := by
      rw [← integral_sq_Lp μ g]
      exact integral_congr_ae (hv.coeFn_toLp.symm.fun_comp fun a : ℝ => a^2)
    rw [heq,Real.sqrt_sq (norm_nonneg g)]
  calc
    _ = ∫ y, ρ y * g y ∂μ := he
    _ = hX.boundedHeat hn p g ⟨D,hg⟩ t ht x := hrep
    _ ≤ |hX.boundedHeat hn p g ⟨D,hg⟩ t ht x| := le_abs_self _
    _ ≤ A*‖g‖ := heval x g ⟨D,hg⟩
    _ = _ := by rw [hnrm]

theorem heatRadonDensity_memLp_two (t : ℝ) (ht : 0 < t) (x : X) :
    MemLp (hX.heatRadonDensity hn p t ht x) 2 (hausdorff n X) := by
  obtain ⟨R,C,hR,hC,hbound⟩ := hX.heatRadonDensity_square_bound hn p t ht
  exact (memLp_two_iff_integrable_sq
    (hX.heatRadonDensity_measurable hn p t ht x).aestronglyMeasurable).mpr (hbound x).1

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
