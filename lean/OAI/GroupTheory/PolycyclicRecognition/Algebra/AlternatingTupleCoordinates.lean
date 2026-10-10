import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearHaarCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FlatSwitchSamples

namespace OAI

/-! # From an ordered tuple to alternating pairs of coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def alternatingTupleSplit (h : ℕ) : (Fin (h + h) → V) ≃L[ℝ] (Fin h → V × V) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u j => (u (Fin.castAdd h j), u (Fin.natAdd h j))
      invFun := fun z => Fin.append (fun j => (z j).1) (fun j => (z j).2)
      left_inv := by
        intro u
        funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.append_left, Fin.append_right]
      right_inv := by intro z; funext j; simp only [Fin.append_left, Fin.append_right]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem alternatingTupleSplit_apply (h : ℕ) (u : Fin (h + h) → V) (j : Fin h) :
    alternatingTupleSplit h u j = (u (Fin.castAdd h j), u (Fin.natAdd h j)) := rfl

end PolycyclicRecognition

end

end OAI
