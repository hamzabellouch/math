import Mathlib
import OAI.Geometry.HyperbolicGroups.RankSampling
import OAI.Geometry.HyperbolicGroups.OriginalLinearFilling
import OAI.Geometry.HyperbolicGroups.GlobalClosedPicture

namespace OAI

noncomputable section

namespace HyperbolicObstruction.IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
open Occurrences.Shape
attribute [local instance] Classical.propDecidable

/-- One cutoff simultaneously enforces the original-letter linear filling and
unbounded closed-picture chain vanishing. It is selected before each alphabet
and realization. -/
def diagramCutoff (m : ℕ) : ℕ :=
  max (original_letter_linear_filling_list (samplingParameter_pos m)
      (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
      (samplingParameter_pos m)).choose
    (uniform_closed_picture_chain_zero.{0,0} (samplingParameter_pos m)
      (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
      (samplingParameter_pos m)).choose

def diagramSelectedStage (m : ℕ) : SamplingStage m (samplingParameter m) :=
  rankSelectedStage diagramCutoff m

/-- Every selected realization has an actual finite-letter linear Dehn bound,
not a radius-limited or surrogate-picture estimate. -/
theorem diagramSelectedStage_linear (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ word : List (LetterPresentation.Alphabet (diagramSelectedStage m).size),
      PresentedGroup.mk (Relator (diagramSelectedStage m).size (diagramSelectedStage m).master
        (diagramSelectedStage m).six) (FreeGroup.mk word) = 1 →
      ∃ a, WordPictures.Homotopy (SimpleWordRelator (diagramSelectedStage m).size
        (diagramSelectedStage m).master (diagramSelectedStage m).six) word [] a ∧
        (a : ℝ) ≤ C * word.length := by
  let h := original_letter_linear_filling_list (samplingParameter_pos m)
    (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
    (samplingParameter_pos m)
  obtain ⟨C,_hM,hC,hh⟩ := h.choose_spec
  refine ⟨C,hC,?_⟩
  apply hh (diagramSelectedStage m).size (diagramSelectedStage m).master (diagramSelectedStage m).six
  exact (rankSelectedStage_good diagramCutoff m).mono (le_max_left _ _)

/-- The SAME selected arrays have vanishing chain for every closed mapped
picture and every abelian coefficient group. No bound on picture size remains.
This does NOT assert their topological asphericity. -/
theorem diagramSelectedStage_chain_zero (m : ℕ)
    (A : Type) [AddCommGroup A]
    (c : Top (diagramSelectedStage m).size (diagramSelectedStage m).master →
      MacroGraph.graph.Dart → A)
    (hc : ∀ a e, c a e.symm = -c a e)
    (f : FrozenCell (diagramSelectedStage m).size (diagramSelectedStage m).master
      (diagramSelectedStage m).six → A)
    (P : WalkPicture.{0} (walkTarget (diagramSelectedStage m).size (diagramSelectedStage m).master
      (diagramSelectedStage m).six c hc f))
    (hm : P.FrozenMapped (walkFrozenTarget (diagramSelectedStage m).size
      (diagramSelectedStage m).master (diagramSelectedStage m).six c hc f)) : P.chain = 0 := by
  let h := uniform_closed_picture_chain_zero.{0,0} (samplingParameter_pos m)
    (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
    (samplingParameter_pos m)
  exact h.choose_spec.2 (diagramSelectedStage m).size (diagramSelectedStage m).master
    (diagramSelectedStage m).six
    ((rankSelectedStage_good diagramCutoff m).mono (le_max_right _ _)) A c hc f P hm

/-- The selected sequence retains ALL the probabilistic conditional sampling
laws used in the obstruction argument; no new sampling hypothesis is required. -/
theorem diagramSamplingSequence : SamplingSequence Field Admissible
    (SamplingStage.Alphabet diagramSelectedStage) (SamplingStage.Matches diagramSelectedStage)
    (SamplingStage.label diagramSelectedStage) :=
  SamplingStage.samplingSequence diagramSelectedStage

end HyperbolicObstruction.IncidenceTemplate
end

end OAI
