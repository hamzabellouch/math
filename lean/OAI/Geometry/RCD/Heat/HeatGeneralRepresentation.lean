import OAI.Geometry.RCD.Heat.HeatJointSymmetry
import OAI.Geometry.RCD.Metric.L2ClippingApproximation

namespace OAI

/-! # Heat density representation on the required L¹ ∩ L² class -/

open Set Filter MeasureTheory Metric TopologicalSpace ProbabilityTheory
open scoped NNReal ENNReal Topology ProbabilityTheory

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonMeasure_ae_integrable (t : ℝ) (ht : 0 < t)
    {f : X → ℝ} (hf : Integrable f (hausdorff n X)) :
    ∀ᵐ x ∂hausdorff n X, Integrable f (hX.heatRadonMeasure hn p t ht x) := by
  apply Measure.ae_integrable_of_integrable_comp (κ := hX.heatMarkovKernel hn p t ht)
  rw [hX.heatMarkovKernel_invariant hn p t ht]
  exact hf

/-- Clipping and invariance extend the pointwise bounded-data
representation to the exact L¹ ∩ L² data class in the published input. -/
theorem heatRadonMeasure_represents (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (hausdorff n X)) (hf : Integrable f (hausdorff n X)) :
    (fun x => ∫ y, f y ∂hX.heatRadonMeasure hn p t ht x) =ᵐ[hausdorff n X]
      heatAt (hausdorff n X) hX.quadratic t f := by
  let μ := hausdorff n X
  let u (i : ℕ) := boundedL2Clip μ i f
  have hbound (i : ℕ) : ∀ᵐ y ∂μ, |u i y| ≤ (i : ℝ≥0) := boundedL2Clip_abs_le μ i f
  have hrep : ∀ᵐ x ∂μ, ∀ i : ℕ,
      (∫ y, clipReal i (f y) ∂hX.heatRadonMeasure hn p t ht x) =
        heatAt μ hX.quadratic t (u i) x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [hX.boundedHeat_represents hn p (u i) ⟨i, hbound i⟩ t ht] with x hx
    calc
      _ = ∫ y, u i y ∂hX.heatRadonMeasure hn p t ht x :=
        integral_congr_ae ((hX.heatRadonMeasure_absolutelyContinuous hn p t ht x).ae_le
          (boundedL2Clip_coe μ i f).symm)
      _ = hX.boundedHeat hn p (u i) ⟨i, hbound i⟩ t ht x :=
        hX.heatRadonMeasure_integral_bounded hn p t ht x (u i) i (hbound i)
      _ = _ := hx.symm
  have hlim : Tendsto (fun i => heatAt μ hX.quadratic t (u i)) atTop
      (𝓝 (heatAt μ hX.quadratic t f)) :=
    (heatAt μ hX.quadratic t).continuous.continuousAt.tendsto.comp (boundedL2Clip_tendsto μ f)
  obtain ⟨a, ha, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [hrep, hae, hX.heatRadonMeasure_ae_integrable hn p t ht hf] with x hx hxa hxi
  have hi : Tendsto (fun j => ∫ y, clipReal (a j) (f y) ∂hX.heatRadonMeasure hn p t ht x)
      atTop (𝓝 (∫ y, f y ∂hX.heatRadonMeasure hn p t ht x)) := by
    apply tendsto_integral_of_dominated_convergence (fun y => ‖f y‖)
    · intro j
      exact ((clipReal_lipschitz (a j)).continuous.comp_aestronglyMeasurable hxi.aestronglyMeasurable)
    · exact hxi.norm
    · intro j
      exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using clipReal_abs_le_self (a j) (f y)
    · exact Eventually.of_forall fun y => (clipReal_nat_tendsto (f y)).comp ha.tendsto_atTop
  simp_rw [hx] at hi
  exact tendsto_nhds_unique hi hxa

theorem heatJointDensity_represents (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (hausdorff n X)) (hf : Integrable f (hausdorff n X)) :
    (fun x => ∫ y, hX.heatJointDensity hn p t ht x y * f y ∂hausdorff n X) =ᵐ[hausdorff n X]
      heatAt (hausdorff n X) hX.quadratic t f := by
  filter_upwards [hX.heatRadonMeasure_represents hn p t ht f hf] with x hx
  calc
    _ = ∫ y, hX.heatRadonDensity hn p t ht x y * f y ∂hausdorff n X := by
      apply integral_congr_ae
      filter_upwards [hX.heatJointDensity_ae hn p t ht x] with y hy
      rw [hy]
    _ = ∫ y, f y ∂hX.heatRadonMeasure hn p t ht x :=
      integral_toReal_rnDeriv_mul (hX.heatRadonMeasure_absolutelyContinuous hn p t ht x)
    _ = _ := hx

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
