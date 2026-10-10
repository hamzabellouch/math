import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! # Polynomial dependence of a nilpotent derivation flow -/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

omit [FiniteDimensional ℝ L] in
theorem nilpotentDerivationFlow_eq_sum {k : ℕ} (hk : D.toLinearMap ^ k = 0)
    (t : ℝ) (x : L) :
    nilpotentDerivationFlow D hD t x =
      ∑ i ∈ Finset.range k, t ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x) := by
  change IsNilpotent.exp (t • D.toLinearMap) x = _
  have ht : (t • D.toLinearMap) ^ k = 0 := by rw [smul_pow, hk, smul_zero]
  rw [IsNilpotent.exp_eq_sum ht]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_pow]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

theorem contDiff_nilpotentDerivationFlow {r : ℕ∞ω} :
    ContDiff ℝ r (fun p : ℝ × L => nilpotentDerivationFlow D hD p.1 p.2) := by
  have hnil := hD
  obtain ⟨k, hk⟩ := hnil
  have heq : (fun p : ℝ × L => nilpotentDerivationFlow D hD p.1 p.2) =
      fun p => ∑ i ∈ Finset.range k,
        p.1 ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) p.2) := by
    funext p
    exact nilpotentDerivationFlow_eq_sum D hD hk p.1 p.2
  rw [heq]
  apply ContDiff.sum
  intro i _
  exact (contDiff_fst.pow i).smul
    ((((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i).toContinuousLinearMap.contDiff).comp contDiff_snd)

end PolycyclicRecognition

end

end OAI
