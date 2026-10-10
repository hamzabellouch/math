import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
namespace DirectionalTransience

theorem tight_iid_difference_translations {E ι : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (ht : IsTightMeasureSet (Set.range fun i =>
      ((μ i).prod (μ i)).map (fun p : E × E => p.1-p.2))) :
    ∃ c : ι → E, IsTightMeasureSet (Set.range fun i => (μ i).map (fun x => x-c i)) := by
  obtain ⟨C,hC,hbound⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (1/4) (by norm_num)
  have hdiff : Measurable (fun p : E × E => p.1-p.2) := measurable_fst.sub measurable_snd
  have hex (i : ι) : ∃ c : E, (μ i) {x | x-c ∉ C} ≤ 1/2 := by
    have h := hbound _ ⟨i,rfl⟩
    rw [Measure.map_apply hdiff hC.measurableSet.compl,
      Measure.prod_apply_symm (hdiff hC.measurableSet.compl)] at h
    by_contra hn
    push Not at hn
    have hh : (1/2 : ℝ≥0∞) ≤ ∫⁻ y, (μ i) {x | x-y ∉ C} ∂μ i := by
      calc _ = ∫⁻ y : E, (1/2 : ℝ≥0∞) ∂μ i := by simp
        _ ≤ _ := lintegral_mono fun y => (hn y).le
    have : (1/2 : ℝ≥0∞) ≤ 1/4 := hh.trans h
    norm_num at this
  choose c hc using hex
  refine ⟨c,isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr ?_⟩
  intro ε hε
  obtain ⟨K,hK,hKb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (ε/2) (ENNReal.div_pos hε.ne' (by norm_num))
  refine ⟨K+C,hK.add hC,?_⟩
  rintro _ ⟨i,rfl⟩
  let A := {x : E | x-c i ∉ K+C}
  let B := {y : E | y-c i ∈ C}
  have hb : (1/2 : ℝ≥0∞) ≤ μ i B := by
    have hc' : μ i Bᶜ ≤ 1/2 := hc i
    have hBm : MeasurableSet B := hC.measurableSet.preimage (measurable_id.sub_const _)
    rw [measure_compl hBm (measure_ne_top _ _),measure_univ] at hc'
    have hh := (tsub_le_iff_right.mp hc')
    apply ENNReal.le_of_add_le_add_left (by norm_num : (1/2 : ℝ≥0∞) ≠ ∞)
    convert hh using 1
    exact ENNReal.add_halves 1
  have hAB : A ×ˢ B ⊆ (fun p : E × E => p.1-p.2) ⁻¹' Kᶜ := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩ hxy
    apply hx
    have he : x-c i = (x-y)+(y-c i) := by abel
    rw [he]
    exact Set.add_mem_add hxy hy
  have hp : μ i A * μ i B ≤ ε/2 := by
    calc _ = (μ i).prod (μ i) (A ×ˢ B) := (Measure.prod_prod _ _).symm
      _ ≤ (μ i).prod (μ i) ((fun p : E × E => p.1-p.2) ⁻¹' Kᶜ) := measure_mono hAB
      _ = ((μ i).prod (μ i)).map (fun p : E × E => p.1-p.2) Kᶜ :=
        (Measure.map_apply hdiff hK.measurableSet.compl).symm
      _ ≤ ε/2 := hKb _ ⟨i,rfl⟩
  change ((μ i).map (fun x => x-c i)) (K+C)ᶜ ≤ ε
  rw [Measure.map_apply (show Measurable (fun x : E => x-c i) by fun_prop) (hK.add hC).measurableSet.compl]
  change μ i A ≤ ε
  have hhalf : μ i A / 2 ≤ ε/2 := by
    calc _ = μ i A * (1/2) := by simp [div_eq_mul_inv]
      _ ≤ μ i A * μ i B := by gcongr
      _ ≤ ε/2 := hp
  calc _ = (μ i A / 2)*2 := (ENNReal.div_mul_cancel (by norm_num) (by norm_num)).symm
    _ ≤ (ε/2)*2 := by gcongr
    _ = ε := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
namespace DirectionalTransience

theorem tight_iid_difference_translations_support {E ι : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (S : ι → Set E) (hS : ∀ i, ∀ᵐ x ∂μ i, x ∈ S i)
    (ht : IsTightMeasureSet (Set.range fun i =>
      ((μ i).prod (μ i)).map (fun p : E × E => p.1-p.2))) :
    ∃ c : ι → E, (∀ i, c i ∈ S i) ∧ IsTightMeasureSet (Set.range fun i => (μ i).map (fun x => x-c i)) := by
  obtain ⟨C,hC,hbound⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (1/4) (by norm_num)
  have hdiff : Measurable (fun p : E × E => p.1-p.2) := measurable_fst.sub measurable_snd
  have hex (i : ι) : ∃ c : E, c ∈ S i ∧ (μ i) {x | x-c ∉ C} ≤ 1/2 := by
    have h := hbound _ ⟨i,rfl⟩
    rw [Measure.map_apply hdiff hC.measurableSet.compl,
      Measure.prod_apply_symm (hdiff hC.measurableSet.compl)] at h
    by_contra hn
    push Not at hn
    have hh : (1/2 : ℝ≥0∞) ≤ ∫⁻ y, (μ i) {x | x-y ∉ C} ∂μ i := by
      calc _ = ∫⁻ y : E, (1/2 : ℝ≥0∞) ∂μ i := by simp
        _ ≤ _ := lintegral_mono_ae ((hS i).mono fun y hy => (hn y hy).le)
    have : (1/2 : ℝ≥0∞) ≤ 1/4 := hh.trans h
    norm_num at this
  choose c hcs hc using hex
  refine ⟨c,hcs,isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr ?_⟩
  intro ε hε
  obtain ⟨K,hK,hKb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (ε/2) (ENNReal.div_pos hε.ne' (by norm_num))
  refine ⟨K+C,hK.add hC,?_⟩
  rintro _ ⟨i,rfl⟩
  let A := {x : E | x-c i ∉ K+C}
  let B := {y : E | y-c i ∈ C}
  have hb : (1/2 : ℝ≥0∞) ≤ μ i B := by
    have hc' : μ i Bᶜ ≤ 1/2 := hc i
    have hBm : MeasurableSet B := hC.measurableSet.preimage (measurable_id.sub_const _)
    rw [measure_compl hBm (measure_ne_top _ _),measure_univ] at hc'
    have hh := (tsub_le_iff_right.mp hc')
    apply ENNReal.le_of_add_le_add_left (by norm_num : (1/2 : ℝ≥0∞) ≠ ∞)
    convert hh using 1
    exact ENNReal.add_halves 1
  have hAB : A ×ˢ B ⊆ (fun p : E × E => p.1-p.2) ⁻¹' Kᶜ := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩ hxy
    apply hx
    have he : x-c i = (x-y)+(y-c i) := by abel
    rw [he]
    exact Set.add_mem_add hxy hy
  have hp : μ i A * μ i B ≤ ε/2 := by
    calc _ = (μ i).prod (μ i) (A ×ˢ B) := (Measure.prod_prod _ _).symm
      _ ≤ (μ i).prod (μ i) ((fun p : E × E => p.1-p.2) ⁻¹' Kᶜ) := measure_mono hAB
      _ = ((μ i).prod (μ i)).map (fun p : E × E => p.1-p.2) Kᶜ :=
        (Measure.map_apply hdiff hK.measurableSet.compl).symm
      _ ≤ ε/2 := hKb _ ⟨i,rfl⟩
  change ((μ i).map (fun x => x-c i)) (K+C)ᶜ ≤ ε
  rw [Measure.map_apply (show Measurable (fun x : E => x-c i) by fun_prop) (hK.add hC).measurableSet.compl]
  change μ i A ≤ ε
  have hhalf : μ i A / 2 ≤ ε/2 := by
    calc _ = μ i A * (1/2) := by simp [div_eq_mul_inv]
      _ ≤ μ i A * μ i B := by gcongr
      _ ≤ ε/2 := hp
  calc _ = (μ i A / 2)*2 := (ENNReal.div_mul_cancel (by norm_num) (by norm_num)).symm
    _ ≤ (ε/2)*2 := by gcongr
    _ = ε := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
