import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraHomLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponentialNaturality
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace OAI

/-! # Recovering represented tangent vectors from exponential lines -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem unitsHomLieDifferential_eq_of_exponential_line
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)))
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) (a : A)
    (he : ∀ t : ℝ, ρ (Exp (t • x)) = algebraExpUnit (t • a)) :
    unitsHomLieDifferential ρ hf x = a := by
  let j := (unitsHomLieDifferential ρ hf).toLinearMap.toContinuousLinearMap
  have hd := hasMFDerivAt_unitsHomLieDifferential ρ hf
  have hbase : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A))
      (fun g => (ρ g : A)) (Exp ((0 : ℝ) • x)) j := by
    rw [zero_smul, hExp.map_zero]
    exact hd
  have hcomp := hbase.comp 0 (hExp.hasMFDerivAt_zero x)
  have hF : HasFDerivAt (fun t : ℝ => (ρ (Exp (t • x)) : A))
      (j.comp (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x)) 0 :=
    hcomp.hasFDerivAt
  have h := hF.hasDerivAt
  change HasDerivAt (fun t : ℝ => (ρ (Exp (t • x)) : A)) (j ((1 : ℝ) • x)) 0 at h
  have hj : j x = unitsHomLieDifferential ρ hf x := rfl
  rw [one_smul, hj] at h
  have h' : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a))
      (unitsHomLieDifferential ρ hf x) 0 := by
    simpa only [he, coe_algebraExpUnit] using h
  have ha : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a)) a 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      (hasDerivAt_exp_smul_const a (0 : ℝ))
  exact h'.unique ha

end PolycyclicRecognition

end

end OAI
