import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped unitInterval

namespace Problem367

theorem measurePreserving_uniform01_projIcc :
    MeasurePreserving (Set.projIcc (0 : ℝ) 1 (by norm_num))
      uniform01 (volume : Measure I) := by
  have hp : Measurable (Set.projIcc (0 : ℝ) 1 (by norm_num)) :=
    continuous_projIcc.measurable
  refine ⟨hp, ?_⟩
  change (volume.restrict (Set.Icc (0 : ℝ) 1)).map _ = _
  rw [← unitInterval.measurePreserving_coe.map_eq,
    Measure.map_map hp measurable_subtype_coe]
  simp only [Function.comp_def, Set.projIcc_val]
  exact Measure.map_id

theorem exists_uniform01_sampler {α : Type*} [MeasurableSpace α]
    [Nonempty α] [StandardBorelSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] :
    ∃ ξ : ℝ → α, Measurable ξ ∧ Measure.map ξ uniform01 = ν := by
  obtain ⟨f, hf, hmap⟩ := ν.exists_measurable_map_eq
  let p : ℝ → I := Set.projIcc 0 1 (by norm_num)
  have hp : Measurable p := measurePreserving_uniform01_projIcc.measurable
  refine ⟨f ∘ p, hf.comp hp, ?_⟩
  rw [← Measure.map_map hf hp]
  change (uniform01.map (Set.projIcc (0 : ℝ) 1 (by norm_num))).map f = ν
  rw [measurePreserving_uniform01_projIcc.map_eq]
  exact hmap

end Problem367

end

end OAI
