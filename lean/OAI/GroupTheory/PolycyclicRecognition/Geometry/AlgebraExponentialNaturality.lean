import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraOneParameter
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieExponential
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace OAI

/-! # Exponential compatibility from the actual algebra-valued derivative -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem hom_exp_eq_algebraExpUnit
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (j : GroupLieAlgebra (𝓘(ℝ, E)) G →L[ℝ] A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1 j)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : ρ (Exp x) = algebraExpUnit (j x) := by
  let f : ℝ → A := fun t => (ρ (Exp (t • x)) : A)
  have hbase : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A))
      (fun g => (ρ g : A)) (Exp ((0 : ℝ) • x)) j := by
    rw [zero_smul, hExp.map_zero]
    exact hd
  have h := hbase.comp 0 (hExp.hasMFDerivAt_zero x)
  have hf : HasDerivAt f (j x) 0 := by
    have hF : HasFDerivAt f
        (j.comp (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x)) 0 :=
      h.hasFDerivAt
    have hh := hF.hasDerivAt
    change HasDerivAt f (j ((1 : ℝ) • x)) 0 at hh
    simpa only [one_smul] using hh
  have hf0 : f 0 = 1 := by
    dsimp only [f]
    rw [zero_smul, hExp.map_zero, map_one]
    rfl
  have hadd (s t : ℝ) : f (s + t) = f s * f t := by
    dsimp only [f]
    rw [hExp.map_add_smul, map_mul]
    rfl
  apply Units.ext
  have heq := oneParameter_eq_exp hf0 hadd hf 1
  simpa only [f, one_smul, coe_algebraExpUnit] using heq

end PolycyclicRecognition

end

end OAI
