import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.BorelAction
import OAI.Geometry.CAT0Fillings.Currents.AffineCalculus

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.BorelCoefficients
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
lemma borelAction_filterContinuity (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (πs : ι → Fin k → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) l (𝓝 (π i x))) :
    Tendsto (fun j => borelAction μ hT b (πs j)) l (𝓝 (borelAction μ hT b π)) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro u hu
  exact borelAction_sequentialContinuity μ hT hμ hb π (fun j => πs (u j))
    (fun i => ⟨(hLip i).choose,fun j => (hLip i).choose_spec (u j)⟩)
    (fun i x => (hpt i x).comp hu)

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma tendsto_toL1_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {fs : ι → X → ℝ} {f G : X → ℝ} (hfs : ∀ j, Integrable (fs j) μ)
    (hf : Integrable f μ) (hG : Integrable G μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖fs j x‖ ≤ G x)
    (hp : ∀ᵐ x ∂μ, Tendsto (fun j => fs j x) l (𝓝 (f x))) :
    Tendsto (fun j => (hfs j).toL1 (fs j)) l (𝓝 (hf.toL1 f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have heq (j) : ‖(hfs j).toL1 (fs j) - hf.toL1 f‖ = ∫ x, ‖fs j x - f x‖ ∂μ := by
    rw [← Integrable.toL1_sub, L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [((hfs j).sub hf).coeFn_toL1] with x hx
    exact congrArg norm hx
  simp only [heq]
  have H := tendsto_integral_filter_of_dominated_convergence (fun x => G x + ‖f x‖)
    (Filter.Eventually.of_forall (fun j => ((hfs j).sub hf).norm.aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun j => (hb j).mono fun x hx =>
      by simpa only [Pi.sub_apply,norm_norm] using
        (norm_sub_le (fs j x) (f x)).trans (add_le_add_left hx _))) (hG.add hf.norm)
    (hp.mono fun x hx => by simpa using (hx.sub_const (f x)).norm)
  simpa using H

lemma borelAction_moving (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [NeBot l]
    {bs : ι → X → ℝ} {b : X → ℝ} (hbs : ∀ j, Integrable (bs j) μ)
    (hb : Integrable b μ)
    (hbpt : Tendsto (fun j => (hbs j).toL1 (bs j)) l (𝓝 (hb.toL1 b)))
    (π : Fin k → X → ℝ) (πs : ι → Fin k → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) l (𝓝 (π i x))) :
    Tendsto (fun j => borelAction μ hT (bs j) (πs j)) l
      (𝓝 (borelAction μ hT b π)) := by
  choose K hK using hLip
  have hfixed := borelAction_filterContinuity μ hT hμ hb π πs
    (fun i => ⟨K i,hK i⟩) hpt
  have hdiff : Tendsto (fun j => borelAction μ hT (bs j) (πs j) -
      borelAction μ hT b (πs j)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (g := fun j => (∏ i, (K i:ℝ)) *
      ‖(hbs j).toL1 (bs j) - hb.toL1 b‖) (fun _ => norm_nonneg _) (fun j => ?_) ?_
    · rw [borelAction_of_integrable μ hT (hbs j) _ (fun i => ⟨K i,hK i j⟩),
        borelAction_of_integrable μ hT hb _ (fun i => ⟨K i,hK i j⟩),← map_sub]
      exact l1Action_bound μ hT hμ (πs j) K (fun i => hK i j) _
    · simpa only [mul_zero] using
        ((tendsto_iff_norm_sub_tendsto_zero.mp hbpt).const_mul (∏ i, (K i:ℝ)))
  simpa only [zero_add,sub_add_cancel] using hdiff.add hfixed

end CAT0Fillings.BorelCoefficients

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)

end CAT0Fillings
end
end

end OAI
