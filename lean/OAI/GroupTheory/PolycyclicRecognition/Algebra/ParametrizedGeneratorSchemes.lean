import OAI.GroupTheory.PolycyclicRecognition.Analysis.ParametrizedSupportPaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorSchemes

namespace OAI

/-! # Continuous path samples for the finite generator schemes

The conjugating letters are fixed. Only the inserted amplitudes vary, so
the whole expanded word has a fixed combinatorial pattern and continuous
amplitudes. This makes each of its support-path samples continuous.
-/

noncomputable section

namespace PolycyclicRecognition

variable {I Y : Type*} {k : ℕ}

def parameterGeneratorSchemeWord (w : Fin k → List (I × ℝ)) (i : Fin k → I)
    (σ : Y → Fin k → ℝ) : List (I × (Y → ℝ)) :=
  (List.ofFn (fun j =>
    (w j).map (fun z => (z.1, fun _ : Y => z.2)) ++
      [(i j, fun y => σ y j)] ++
      (inverseGeneratorWord (w j)).map (fun z => (z.1, fun _ : Y => z.2)))).flatten

theorem parameterGeneratorSchemeWord_eval (w : Fin k → List (I × ℝ)) (i : Fin k → I)
    (σ : Y → Fin k → ℝ) (y : Y) :
    (parameterGeneratorSchemeWord w i σ).map (fun z => (z.1, z.2 y)) =
      generatorSchemeWord w i (σ y) := by
  simp [parameterGeneratorSchemeWord, generatorSchemeWord, List.map_flatten,
    List.map_ofFn, List.map_map, Function.comp_def]

variable [TopologicalSpace Y]

theorem parameterGeneratorSchemeWord_continuous (w : Fin k → List (I × ℝ))
    (i : Fin k → I) (σ : Y → Fin k → ℝ) (hσ : Continuous σ) :
    ∀ z ∈ parameterGeneratorSchemeWord w i σ, Continuous z.2 := by
  intro z hz
  obtain ⟨v, hv, hz⟩ := List.mem_flatten.mp hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
  have hconst (v : List (I × ℝ)) (z : I × (Y → ℝ))
      (hz : z ∈ v.map (fun a => (a.1, fun _ : Y => a.2))) : Continuous z.2 := by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
    exact continuous_const
  rcases List.mem_append.mp hz with hz | hz
  · rcases List.mem_append.mp hz with hz | hz
    · exact hconst _ z hz
    · have he : z = (i j, fun y => σ y j) := by simpa using hz
      rw [he]
      exact (continuous_apply j).comp hσ
  · exact hconst _ z hz

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1)

/-- Evaluating a chosen finite scheme through continuous local inverse
coordinates gives continuous, hence Borel, fixed-time path samples. -/
theorem continuous_generatorScheme_path_sample
    (w : Fin k → List (I × ℝ)) (i : Fin k → I)
    (σ : Y → Fin k → ℝ) (hσ : Continuous σ)
    (n : Y → G) (hn : Continuous n) (d₀ : G) (r : ℝ) (t : unitInterval) :
    Continuous (fun y => supportWordPath d f hd hf hd₀ hf₀ d₀ r
      (generatorSchemeWord w i (σ y)) (n y) t) := by
  have h := continuous_supportWordPath_sample d f hd hf hd₀ hf₀ d₀ r
    (parameterGeneratorSchemeWord w i σ)
    (parameterGeneratorSchemeWord_continuous w i σ hσ) n hn t
  have he : (fun y => supportWordPath d f hd hf hd₀ hf₀ d₀ r
      ((parameterGeneratorSchemeWord w i σ).map (fun z => (z.1, z.2 y))) (n y) t) =
      fun y => supportWordPath d f hd hf hd₀ hf₀ d₀ r
        (generatorSchemeWord w i (σ y)) (n y) t := by
    funext y
    exact congrArg (fun u => supportWordPath d f hd hf hd₀ hf₀ d₀ r u (n y) t)
      (parameterGeneratorSchemeWord_eval w i σ y)
  rw [← he]
  exact h

end PolycyclicRecognition

end

end OAI
