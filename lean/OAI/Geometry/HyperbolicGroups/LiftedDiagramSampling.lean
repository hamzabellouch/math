import Mathlib
import OAI.Geometry.HyperbolicGroups.SelectedPresentation
import OAI.Geometry.HyperbolicGroups.DiagramSampling
import OAI.Geometry.HyperbolicGroups.ActualLiftedChain

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
open Occurrences.Shape
attribute [local instance] Classical.propDecidable

/-- A single diagonal cutoff for filling and the full LIFTED chain statement.
Nothing about a future picture, action, word, or deck group is sampled later. -/
def finalDiagramCutoff (m : ℕ) : ℕ :=
  max (diagramCutoff m)
    (uniform_actual_lifted_chain_zero.{0,0,0} (samplingParameter_pos m)
      (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
      (samplingParameter_pos m)).choose

def finalDiagramStage (m : ℕ) : SamplingStage m (samplingParameter m) :=
  rankSelectedStage finalDiagramCutoff m

lemma finalDiagramStage_good (m : ℕ) :
    Occurrences.GoodUpTo (finalDiagramCutoff m) (samplingParameter m) (8*samplingParameter m)
      (samplingParameter m) (Sum.elim (finalDiagramStage m).master (finalDiagramStage m).six) :=
  rankSelectedStage_good finalDiagramCutoff m

/-- Finite-letter linear filling for the same final selected arrays. -/
theorem finalDiagramStage_linear (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ word : List (LetterPresentation.Alphabet (finalDiagramStage m).size),
      PresentedGroup.mk (Relator (finalDiagramStage m).size (finalDiagramStage m).master
        (finalDiagramStage m).six) (FreeGroup.mk word) = 1 →
      ∃ a, WordPictures.Homotopy (SimpleWordRelator (finalDiagramStage m).size
        (finalDiagramStage m).master (finalDiagramStage m).six) word [] a ∧
        (a : ℝ) ≤ C * word.length := by
  let h := original_letter_linear_filling_list (samplingParameter_pos m)
    (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
    (samplingParameter_pos m)
  obtain ⟨C,_hM,hC,hh⟩ := h.choose_spec
  refine ⟨C,hC,?_⟩
  apply hh (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six
  exact (finalDiagramStage_good m).mono ((le_max_left _ _).trans (le_max_left _ _))

/-- All lifted cellular coefficients vanish for every mapped spherical picture
for the final selected arrays. Unlike projected chain sums, coefficients for
different deck translates of one cell may be chosen independently. -/
theorem finalDiagramStage_lifted_chain_zero (m : ℕ)
    (G : Type) [Group G] (A : Type) [AddCommGroup A]
    (voltage : Dart (finalDiagramStage m).size (finalDiagramStage m).master → G)
    (hv : ∀ e, voltage (rev (finalDiagramStage m).size (finalDiagramStage m).master e) = (voltage e)⁻¹)
    (hcell : ∀ a : Cell (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six,
      (List.ofFn (fun i => voltage (side (finalDiagramStage m).size (finalDiagramStage m).master
        (finalDiagramStage m).six a i))).prod = 1)
    (c : G → Top (finalDiagramStage m).size (finalDiagramStage m).master → MacroGraph.graph.Dart → A)
    (hc : ∀ g a e, c g a e.symm = -c g a e)
    (f : G → FrozenCell (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six → A)
    (P : WalkPicture.{0} (liftedWalkTarget (finalDiagramStage m).size (finalDiagramStage m).master
      (finalDiagramStage m).six voltage hv hcell c hc f))
    (hm : P.FrozenMapped (liftedFrozenTarget (finalDiagramStage m).size (finalDiagramStage m).master
      (finalDiagramStage m).six voltage hv hcell c hc f)) : P.chain = 0 := by
  let h := uniform_actual_lifted_chain_zero.{0,0,0} (samplingParameter_pos m)
    (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
    (samplingParameter_pos m)
  exact h.choose_spec.2 (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six
    ((finalDiagramStage_good m).mono (le_max_right _ _)) G A voltage hv hcell c hc f P hm

theorem finalDiagramSamplingSequence : SamplingSequence Field Admissible
    (SamplingStage.Alphabet finalDiagramStage) (SamplingStage.Matches finalDiagramStage)
    (SamplingStage.label finalDiagramStage) :=
  SamplingStage.samplingSequence finalDiagramStage

/-- If every selected letter group is infinite, then all sufficiently late
groups admit no geometric CAT(0) action. -/
theorem finalDiagramStage_eventually_noAction
    [∀ m, Infinite (SamplingStage.LetterGroup finalDiagramStage m)] :
    ∀ᶠ m in Filter.atTop, NoGeometricCATZeroAction (SamplingStage.LetterGroup finalDiagramStage m) :=
  SamplingStage.eventually_noAction finalDiagramStage

end HyperbolicObstruction.IncidenceTemplate
end
end

section

end
end

end OAI
