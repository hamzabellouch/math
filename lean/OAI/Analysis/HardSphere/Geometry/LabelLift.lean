import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothMultiplier
import OAI.Analysis.HardSphere.Geometry.HeadLift

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def labelLift (n : ℕ) (i : Fin n) : LiftedConfiguration n →L[ℝ] LiftedConfiguration 1 :=
  .pi fun _ ↦ .proj i

def SmoothMultiplier.liftLabel {L : Length} (w : SmoothMultiplier 1 L) (n : ℕ) (i : Fin n) :
    SmoothMultiplier n L := .ofSmooth (fun X ↦ w.orbital (X i)) (w.smooth.comp (labelLift n i).contDiff)

lemma SmoothMultiplier.partial_liftLabel {L : Length} (w : SmoothMultiplier 1 L)
    (n : ℕ) (i : Fin n) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (w.liftLabel n i).toFun p X=
      if p.1=i then coordDerivative 1 L w.toFun (0,p.2) (fun _ ↦ X i) else 0 := by
  classical
  have h := (w.smooth.differentiable (by simp)
    (labelLift n i (representative n L X))).hasFDerivAt.comp
    (representative n L X) (labelLift n i).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration 1 ↦ w.toFun (project 1 L Y)) ∘ labelLift n i)
    (representative n L X)) (Pi.single p.1 (Pi.single p.2 1))=_
  rw [h.fderiv,ContinuousLinearMap.comp_apply]
  by_cases hp : p.1=i
  · rw [ite_eq_left hp]
    have hd : labelLift n i (Pi.single p.1 (Pi.single p.2 1))=Pi.single 0 (Pi.single p.2 1) := by
      ext k j
      have hk : k=0 := Subsingleton.elim _ _
      subst k
      simp [labelLift,hp]
    rw [hd]
    rfl
  · rw [ite_eq_right hp]
    have hd : labelLift n i (Pi.single p.1 (Pi.single p.2 1))=0 := by
      ext k j
      simp [labelLift,Ne.symm hp]
    rw [hd,map_zero]

def SmoothMultiplier.sum {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) : SmoothMultiplier n L :=
  .ofSmooth (fun X ↦ ∑ s, (w s).toFun X) (ContDiff.sum fun s _ ↦ (w s).smooth)

lemma SmoothMultiplier.partial_sum {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (SmoothMultiplier.sum w).toFun p X=∑ s, coordDerivative n L (w s).toFun p X := by
  unfold coordDerivative
  change (fderiv ℝ (fun Y ↦ ∑ s, (w s).toFun (project n L Y)) _) _ = _
  rw [fderiv_fun_sum (fun s _ ↦ (w s).smooth.differentiable (by simp) _),sum_apply]

end HardSphere

end

end OAI
