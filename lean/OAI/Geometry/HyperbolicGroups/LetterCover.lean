import Mathlib
import OAI.Geometry.HyperbolicGroups.LiftedBasis

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The actual original marked presentation supplies the deck labels, via
fixed fan routes; the larger auxiliary polygon bouquet group is not used. -/
def letterVoltage (e : Dart n w) : LetterPresentation.Group n w d :=
  PresentedGroup.mk (Relator n w d) (FreeGroup.mk (collapse n w e))

lemma letterVoltage_rev (e : Dart n w) :
    letterVoltage n w d (rev n w e) = (letterVoltage n w d e)⁻¹ := by
  simp only [letterVoltage,collapse_rev,← FreeGroup.inv_mk,map_inv]

lemma letterVoltage_word (z : List (Dart n w)) :
    (z.map (letterVoltage n w d)).prod =
      PresentedGroup.mk (Relator n w d) (FreeGroup.mk (z.flatMap (collapse n w))) := by
  induction z with
  | nil => simp only [List.map_nil,List.prod_nil,List.flatMap_nil,← FreeGroup.one_eq_mk,map_one]
  | cons e z ih =>
    simp only [List.map_cons,List.prod_cons,List.flatMap_cons,← FreeGroup.mul_mk,map_mul,← ih]
    rfl

lemma letterVoltage_cell (a : Cell n w d) :
    (List.ofFn (fun i => letterVoltage n w d (side n w d a i))).prod = 1 := by
  have heq := letterVoltage_word n w d (List.ofFn (side n w d a))
  simp only [List.map_ofFn,Function.comp_def] at heq
  rw [heq]
  obtain ⟨_, _, filling⟩ := cell_collapse_filling n w d a
  have he := WordPictures.sound filling
  apply PresentedGroup.mk_eq_one_iff.mpr
  have hm := PresentedGroup.mk_eq_one_iff.mp he
  rw [simple_presentation_normalClosure] at hm
  exact hm

lemma letterVoltage_letter (a : Alphabet n) :
    letterVoltage n w d (letterDart n w a) = LetterPresentation.letter n w d a := by
  simp only [letterVoltage,collapse_letter,LetterPresentation.letter,freeLetter_mk]

/-- A fully constructed cover target for the actual letter quotient. Its
relation equations are theorems, not assumptions of the chain conclusion. -/
def letterGroupCover := actualCellCover n w d (letterVoltage n w d)
  (letterVoltage_rev n w d) (letterVoltage_cell n w d)

def letterIntegralTarget := integralLiftedTarget n w d (LetterPresentation.Group n w d)
  (letterVoltage n w d) (letterVoltage_rev n w d) (letterVoltage_cell n w d)

def letterIntegralFrozenTarget := integralLiftedFrozenTarget n w d (LetterPresentation.Group n w d)
  (letterVoltage n w d) (letterVoltage_rev n w d) (letterVoltage_cell n w d)

/-- Uniformly in every realization of the original arrays, not a scalar
projection and not a conclusion conditional on cover equations. -/
theorem uniform_letter_integral_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ P : WalkPicture.{u} (letterIntegralTarget n w d),
        P.FrozenMapped (letterIntegralFrozenTarget n w d) → P.chain = 0 := by
  obtain ⟨M,hM,hh⟩ := uniform_integral_lifted_chain_zero.{u,0} ha hb hd
  refine ⟨M,hM,?_⟩
  intro n w d hgood P hm
  exact hh n w d hgood _ _ (letterVoltage_rev n w d) (letterVoltage_cell n w d) P hm

/-- For the SAME independently sampled presentation, every spherical picture
with its actual original-group lift has zero full integral cell vector.
Infinitude and identification with the topological universal cover are NOT
asserted by this combinatorial theorem. -/
theorem finalDiagramStage_letter_chain_zero (m : ℕ)
    (P : WalkPicture.{0} (letterIntegralTarget (finalDiagramStage m).size
      (finalDiagramStage m).master (finalDiagramStage m).six))
    (hm : P.FrozenMapped (letterIntegralFrozenTarget (finalDiagramStage m).size
      (finalDiagramStage m).master (finalDiagramStage m).six)) : P.chain = 0 :=
  finalDiagramStage_integral_chain_zero m _ _
    (letterVoltage_rev _ _ _) (letterVoltage_cell _ _ _) P hm

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
