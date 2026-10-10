import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothMultiplier
import OAI.Analysis.HardSphere.Geometry.TorusLiftBox

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

def headLift (n : ℕ) : LiftedConfiguration (n+1) →L[ℝ] LiftedConfiguration 1 :=
  .pi fun _ ↦ .proj 0

lemma headLift_direction_zero (n : ℕ) (j : Fin 3) :
    headLift n (Pi.single 0 (Pi.single j 1))=Pi.single 0 (Pi.single j 1) := by
  ext i k
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  simp [headLift]

lemma headLift_direction_succ (n : ℕ) (i : Fin n) (j : Fin 3) :
    headLift n (Pi.single i.succ (Pi.single j 1))=0 := by
  ext k q
  simp [headLift]

def SmoothMultiplier.orbital {L : Length} (w : SmoothMultiplier 1 L) (x : Torus L) : ℂ :=
  w.toFun (fun _ ↦ x)

lemma SmoothMultiplier.orbital_continuous {L : Length} (w : SmoothMultiplier 1 L) :
    Continuous w.orbital :=
  (continuous_of_continuous_lift w.smooth.continuous).comp (continuous_pi fun _ ↦ continuous_id)

def SmoothMultiplier.orbitalBound {L : Length} (w : SmoothMultiplier 1 L) : ℝ :=
  ‖(⟨w.orbital,w.orbital_continuous⟩ : C(Torus L,ℂ))‖^2

lemma SmoothMultiplier.orbital_le_bound {L : Length} (w : SmoothMultiplier 1 L) (x : Torus L) :
    ‖w.orbital x‖^2≤w.orbitalBound := by
  exact pow_le_pow_left₀ (norm_nonneg _) ((⟨w.orbital,w.orbital_continuous⟩ : C(Torus L,ℂ)).norm_coe_le_norm x) 2

def SmoothMultiplier.orbitalEnergy {L : Length} (w : SmoothMultiplier 1 L) : ℝ :=
  ∑ j : Fin 3, ∫ x : Torus L, ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ x)‖^2

def SmoothMultiplier.liftHead {L : Length} (w : SmoothMultiplier 1 L) (n : ℕ) :
    SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ w.orbital (X 0)) (w.smooth.comp (headLift n).contDiff)

lemma SmoothMultiplier.coordDerivative_liftHead_zero {L : Length}
    (w : SmoothMultiplier 1 L) (n : ℕ) (j : Fin 3) :
    coordDerivative (n+1) L (w.liftHead n).toFun (0,j)=
      fun X ↦ coordDerivative 1 L w.toFun (0,j) (fun _ ↦ X 0) := by
  funext X
  have h := (w.smooth.differentiable (by simp)
    (headLift n (representative (n+1) L X))).hasFDerivAt.comp
    (representative (n+1) L X) (headLift n).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration 1 ↦ w.toFun (project 1 L Y)) ∘ headLift n)
    (representative (n+1) L X)) (Pi.single 0 (Pi.single j 1))=_
  rw [h.fderiv,ContinuousLinearMap.comp_apply,headLift_direction_zero]
  rfl

lemma SmoothMultiplier.coordDerivative_liftHead_succ {L : Length}
    (w : SmoothMultiplier 1 L) (n : ℕ) (i : Fin n) (j : Fin 3) :
    coordDerivative (n+1) L (w.liftHead n).toFun (i.succ,j)=0 := by
  funext X
  have h := (w.smooth.differentiable (by simp)
    (headLift n (representative (n+1) L X))).hasFDerivAt.comp
    (representative (n+1) L X) (headLift n).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration 1 ↦ w.toFun (project 1 L Y)) ∘ headLift n)
    (representative (n+1) L X)) (Pi.single i.succ (Pi.single j 1))=0
  rw [h.fderiv,ContinuousLinearMap.comp_apply,headLift_direction_succ,map_zero]

lemma SmoothMultiplier.liftHead_gradient_sum {L : Length}
    (w : SmoothMultiplier 1 L) (n : ℕ) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (w.liftHead n).toFun p X‖^2)=
      ∑ j : Fin 3, ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ X 0)‖^2 := by
  rw [Fintype.sum_prod_type,Fin.sum_univ_succ]
  simp only [w.coordDerivative_liftHead_zero,w.coordDerivative_liftHead_succ,
    Pi.zero_apply,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero]

end HardSphere

end

end OAI
