import Mathlib
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves
import OAI.Analysis.Conductivity.Geometry.BoxIteration

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def boxCoordinates : Coord3 ≃L[ℝ] Box3 :=
  (show Coord3 ≃ₗ[ℝ] Box3 from
    { toFun := fun x => ((x 0,x 1),x 2)
      invFun := fun p => ![p.1.1,p.1.2,p.2]
      left_inv := by intro x; ext i; fin_cases i <;> rfl
      right_inv := by intro p; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }).toContinuousLinearEquiv

lemma boxCoordinates_apply (x : Coord3) : boxCoordinates x=((x 0,x 1),x 2) := rfl
lemma boxCoordinates_symm_apply (p : Box3) : boxCoordinates.symm p=![p.1.1,p.1.2,p.2] := rfl

lemma boxCoordinates_volume : MeasurePreserving boxCoordinates := by
  exact (volume_preserving_prodAssoc.symm (MeasurableEquiv.prodAssoc : Box3≃ᵐ ℝ×(ℝ×ℝ))).comp
    threeArrow_volume

lemma boxCoordinates_integral (f : Box3 → ℝ) :
    (∫ x,f (boxCoordinates x))=(∫ p,f p) :=
  boxCoordinates_volume.integral_comp boxCoordinates.toHomeomorph.measurableEmbedding f

lemma boxCoordinates_integral_symm (f : Coord3 → ℝ) :
    (∫ p,f (boxCoordinates.symm p))=(∫ x,f x) := by
  have h := boxCoordinates_integral (fun p => f (boxCoordinates.symm p))
  simpa only [boxCoordinates.symm_apply_apply] using h.symm

lemma boxCoordinates_fderiv (f : Box3 → ℝ) (hf : Differentiable ℝ f)
    (x v : Coord3) :
    fderiv ℝ (f∘boxCoordinates) x v=fderiv ℝ f (boxCoordinates x) (boxCoordinates v) := by
  rw [fderiv_comp x (hf _) boxCoordinates.differentiableAt]
  have he : fderiv ℝ (fun x => boxCoordinates x) x=boxCoordinates.toContinuousLinearMap :=
    boxCoordinates.toContinuousLinearMap.hasFDerivAt.fderiv
  rw [he]
  rfl

end ScalarConductivity

end

end OAI
