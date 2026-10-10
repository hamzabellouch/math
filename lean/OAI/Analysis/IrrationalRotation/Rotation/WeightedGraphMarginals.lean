import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.WeightedGraphMarginals

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_fst_graph (μ : Measure X) {T : X → Y} (hT : Measurable T) :
    (μ.map (fun x => (x, T x))).map Prod.fst = μ := by
  have hg : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  rw [Measure.map_map measurable_fst hg]
  change μ.map id = μ
  exact Measure.map_id

theorem map_snd_graph (μ : Measure X) {T : X → Y} (hT : Measurable T) :
    (μ.map (fun x => (x, T x))).map Prod.snd = μ.map T := by
  have hg : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  rw [Measure.map_map measurable_snd hg]
  rfl

theorem map_withDensity_inverse (μ : Measure X) {T S : X → X}
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : ∀ x, S (T x) = x) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map T = μ.withDensity (fun y => f (S y)) := by
  ext s hs
  rw [Measure.map_apply hT.measurable hs,
    withDensity_apply _ (hT.measurable hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hT.measurable hs), ← lintegral_indicator hs]
  have h := hT.lintegral_comp ((hf.comp hS).indicator hs)
  convert h using 1 <;> apply lintegral_congr <;> intro x <;>
    simp only [Set.indicator, Function.comp_apply, Set.mem_preimage, hST]
  all_goals rfl

theorem withDensity_finset_sum {ι : Type*} (μ : Measure X) (s : Finset ι)
    (f : ι → X → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) :
    μ.withDensity (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, μ.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, Measurable (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simp only [Finset.sum_insert ha]
      rw [show (fun x => f a x + ∑ i ∈ s, f i x) =
        f a + (fun x => ∑ i ∈ s, f i x) from rfl,
        withDensity_add_left hfa, ih hfs]

theorem map_finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure X)
    {T : X → Y} (hT : Measurable T) :
    (∑ i ∈ s, μ i).map T = ∑ i ∈ s, (μ i).map T := by
  simp only [← Measure.mapₗ_apply_of_measurable hT, map_sum]

theorem withDensity_real_finset_sum {ι : Type*} (μ : Measure X) (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i ∈ s, Measurable (f i))
    (hfnonneg : ∀ i ∈ s, ∀ x, 0 ≤ f i x) {c : ℝ} (hc : 0 ≤ c) :
    μ.withDensity (fun x => ENNReal.ofReal (c * ∑ i ∈ s, f i x)) =
      ENNReal.ofReal c • ∑ i ∈ s, μ.withDensity (fun x => ENNReal.ofReal (f i x)) := by
  have he : (fun x => ENNReal.ofReal (c * ∑ i ∈ s, f i x)) =
      ENNReal.ofReal c • (fun x => ∑ i ∈ s, ENNReal.ofReal (f i x)) := by
    funext x
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_sum_of_nonneg
      (fun i hi => hfnonneg i hi x)]
    rfl
  rw [he, withDensity_smul]
  · rw [withDensity_finset_sum μ s _ (fun i hi => (hf i hi).ennreal_ofReal)]
  · exact Finset.measurable_sum s (fun i hi => (hf i hi).ennreal_ofReal)

end Invariant233.WeightedGraphMarginals

end

end OAI
