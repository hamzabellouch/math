import OAI.Geometry.TranslativeCovering.BlockDimension

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1

namespace MeasureCut

lemma continuous_cdf (ν : Measure ℝ) [IsFiniteMeasure ν] [NullSingletonClass ν] :
    Continuous (fun x : ℝ => ν.real (Iic x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (x+1)) ν :=
    (integrable_const (1 : ℝ)).integrableOn
  have hc := hi.continuousOn_Iic_primitive_Iic
  have heq : (fun y : ℝ => ∫ t in Iic y, (1 : ℝ) ∂ν) =
      (fun y : ℝ => ν.real (Iic y)) := by
    funext y
    simp [integral_const, measureReal_def]
  rw [heq] at hc
  exact hc.continuousAt (Iic_mem_nhds (by linarith))

lemma cdf_atBot (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Tendsto (fun x : ℝ => ν.real (Iic x)) atBot (nhds 0) := by
  have hi : (⋂ x : ℝ, Iic x) = ∅ := by
    ext y
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
    intro h
    have := h (y-1)
    linarith
  have ht := tendsto_measure_iInter_atBot
    (fun x : ℝ => (measurableSet_Iic : MeasurableSet (Iic x)).nullMeasurableSet (μ := ν))
    (fun x y h => Iic_subset_Iic.mpr h) ⟨0, measure_ne_top ν _⟩
  rw [hi, measure_empty] at ht
  simpa only [Function.comp_def, ENNReal.toReal_zero, measureReal_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp ht

lemma exists_cdf_eq (ν : Measure ℝ) [IsFiniteMeasure ν] [NullSingletonClass ν]
    {r : ℝ} (hr : 0 < r) (hr' : r < ν.real univ) :
    ∃ x : ℝ, ν.real (Iic x) = r := by
  have ht : Tendsto (fun x : ℝ => ν.real (Iic x)) atTop (nhds (ν.real univ)) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top ν univ)).comp (tendsto_measure_Iic_atTop ν)
  have hab := isPreconnected_univ.intermediate_value_Ioo
    (by simp) (by simp) (continuous_cdf ν).continuousOn (cdf_atBot ν) ht ⟨hr, hr'⟩
  simpa only [mem_image, mem_univ, true_and] using hab

lemma exists_subset_measure {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {E : Set Ω} (hE : MeasurableSet E) {r : ℝ}
    (hr : 0 ≤ r) (hrE : r ≤ μ.real E) :
    ∃ A : Set Ω, MeasurableSet A ∧ A ⊆ E ∧ μ.real A = r := by
  classical
  by_cases hzero : r = 0
  · exact ⟨∅, MeasurableSet.empty, empty_subset _, by simp [hzero]⟩
  by_cases hfull : r = μ.real E
  · exact ⟨E, hE, Subset.rfl, hfull.symm⟩
  let f := embeddingReal Ω
  have hf : MeasurableEmbedding f := measurableEmbedding_embeddingReal Ω
  let ν := (μ.restrict E).map f
  have : IsFiniteMeasure ν := inferInstance
  have : NullSingletonClass ν := ⟨fun x => by
    rw [show ν {x} = (μ.restrict E) (f ⁻¹' {x}) from hf.map_apply _ _]
    exact (Set.subsingleton_singleton.preimage hf.injective).measure_zero _⟩
  have htotal : ν.real univ = μ.real E := by
    simp [ν, measureReal_def, hf.map_apply]
  obtain ⟨x,hx⟩ := exists_cdf_eq ν (lt_of_le_of_ne hr (Ne.symm hzero))
    (by rw [htotal]; exact lt_of_le_of_ne hrE hfull)
  refine ⟨E ∩ f ⁻¹' Iic x, hE.inter (hf.measurable measurableSet_Iic), inter_subset_left, ?_⟩
  rw [← hx, measureReal_def, measureReal_def, hf.map_apply, Measure.restrict_apply
    (hf.measurable measurableSet_Iic)]
  congr 1
  exact congrArg μ (inter_comm _ _)

end MeasureCut

end OAI
