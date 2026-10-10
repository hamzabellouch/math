import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory
open scoped unitInterval

namespace Problem336

def clampUniform : ℝ → I := Set.projIcc 0 1 zero_le_one

@[fun_prop]
theorem measurable_clampUniform : Measurable clampUniform :=
  continuous_projIcc.measurable

theorem uniform01_eq_map_unitInterval :
    uniform01 = (volume : Measure I).map (fun x : I => (x : ℝ)) :=
  unitInterval.measurePreserving_coe.map_eq.symm

theorem map_clampUniform : uniform01.map clampUniform = (volume : Measure I) := by
  rw [uniform01_eq_map_unitInterval,
    Measure.map_map measurable_clampUniform measurable_subtype_coe]
  convert (Measure.map_id : (volume : Measure I).map id = volume) using 1
  congr 1
  funext x
  exact Set.projIcc_val zero_le_one x

theorem exists_uniform01_sampler {Y : Type*} [MeasurableSpace Y]
    [Nonempty Y] [StandardBorelSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ] :
    ∃ f : ℝ → Y, Measurable f ∧ uniform01.map f = μ := by
  obtain ⟨f, hf, hmap⟩ := μ.exists_measurable_map_eq
  refine ⟨f ∘ clampUniform, hf.comp measurable_clampUniform, ?_⟩
  rw [← Measure.map_map hf measurable_clampUniform, map_clampUniform, hmap]

theorem sampler_uniform01_probability : IsProbabilityMeasure uniform01 := by
  rw [uniform01_eq_map_unitInterval]
  exact inferInstance

local instance : IsProbabilityMeasure uniform01 := sampler_uniform01_probability

def privatePoolLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => uniform01)

theorem privatePoolLaw_probability : IsProbabilityMeasure privatePoolLaw := by
  unfold privatePoolLaw
  infer_instance

local instance : IsProbabilityMeasure privatePoolLaw := privatePoolLaw_probability

def keyPoolLaw : Measure (ℝ × (ℕ → ℝ)) := uniform01.prod privatePoolLaw

theorem keyPoolLaw_probability : IsProbabilityMeasure keyPoolLaw := by
  unfold keyPoolLaw
  infer_instance

local instance : IsProbabilityMeasure keyPoolLaw := keyPoolLaw_probability

def splitVertexLabel : ℝ → ℝ × (ℕ → ℝ) :=
  Classical.choose (exists_uniform01_sampler keyPoolLaw)

@[fun_prop]
theorem measurable_splitVertexLabel : Measurable splitVertexLabel :=
  (Classical.choose_spec (exists_uniform01_sampler keyPoolLaw)).1

theorem map_splitVertexLabel : uniform01.map splitVertexLabel = keyPoolLaw :=
  (Classical.choose_spec (exists_uniform01_sampler keyPoolLaw)).2

theorem exists_uniform01_kernel_sampler {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [Nonempty Y] [StandardBorelSpace Y]
    (κ : ProbabilityTheory.Kernel X Y) [ProbabilityTheory.IsMarkovKernel κ] :
    ∃ f : X → ℝ → Y, Measurable (Function.uncurry f) ∧
      ∀ x, uniform01.map (f x) = κ x := by
  obtain ⟨f, hf, hmap⟩ := κ.exists_measurable_map_eq_unitInterval
  refine ⟨fun x r => f x (clampUniform r), ?_, ?_⟩
  · exact hf.comp (measurable_fst.prodMk (measurable_clampUniform.comp measurable_snd))
  · intro x
    change uniform01.map (f x ∘ clampUniform) = κ x
    rw [← Measure.map_map hf.of_uncurry_left measurable_clampUniform,
      map_clampUniform, hmap]

theorem map_splitVertexLabels :
    (Measure.infinitePi (fun _ : ℕ => uniform01)).map
      (fun U : ℕ → ℝ => fun v => splitVertexLabel (U v)) =
      Measure.infinitePi (fun _ : ℕ => keyPoolLaw) := by
  rw [Measure.infinitePi_map_pi]
  · simp only [map_splitVertexLabel]
  · intro v
    exact measurable_splitVertexLabel

end Problem336

end

end OAI
