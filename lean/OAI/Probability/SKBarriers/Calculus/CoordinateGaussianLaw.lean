import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyJointMoment
import OAI.Probability.SKBarriers.Gaussian.FiberGaussian

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def coordinateArray (n : ℕ) (z : ParameterSpace n) : Fin n → ℝ :=
  fun i => coordinateProjection n i z

theorem coordinateArray_continuous (n : ℕ) : Continuous (coordinateArray n) :=
  continuous_pi (fun i => (coordinateProjection n i).continuous)

theorem coordinateArray_measurePreserving (n : ℕ) (x : ℝ) :
    MeasurePreserving (coordinateArray n) (fiberGaussian n x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  induction n with
  | zero =>
    refine ⟨(coordinateArray_continuous 0).measurable,?_⟩
    rw [fiberGaussian,Measure.map_dirac' (coordinateArray_continuous 0).measurable,
      Measure.pi_of_empty _ (coordinateArray 0 x)]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)
    have he : MeasurePreserving e (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
        ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
      measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) (Fin.last n)
    have hprod := (Measure.measurePreserving_swap (μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (ν := gaussianReal 0 1)).comp (ih.prod (MeasurePreserving.id (gaussianReal 0 1)))
    have H := he.symm.comp hprod
    convert H using 1 <;> try rfl
    funext z
    apply e.injective
    rw [Function.comp_apply,e.apply_symm_apply]
    apply Prod.ext
    · simp [e,coordinateArray,coordinateProjection]
    · funext i
      simp [e,coordinateArray,coordinateProjection,Fin.init]

def enumeratedDisorder (N : ℕ) (z : ParameterSpace (Fintype.card (Edge N))) : Disorder N :=
  fun e => coordinateProjection (Fintype.card (Edge N)) ((Fintype.equivFin (Edge N)) e) z

theorem enumeratedDisorder_measurePreserving (N : ℕ) (x : ℝ) :
    MeasurePreserving (enumeratedDisorder N) (fiberGaussian (Fintype.card (Edge N)) x)
      (disorderLaw N) := by
  have H := (measurePreserving_piCongrLeft (fun _ : Edge N => gaussianReal 0 1)
    (Fintype.equivFin (Edge N)).symm).comp (coordinateArray_measurePreserving (Fintype.card (Edge N)) x)
  convert H using 1
  · funext z e
    simp [enumeratedDisorder, coordinateArray, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · rfl
end SK.Analytic

end
end

end

end OAI
