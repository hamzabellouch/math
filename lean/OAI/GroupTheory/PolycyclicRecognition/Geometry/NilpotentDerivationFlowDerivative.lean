import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlowSmooth
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! # The initial velocity of a nilpotent derivation flow -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

omit [FiniteDimensional ℝ L] in
theorem hasDerivAt_nilpotentDerivationFlow_zero (x : L) :
    HasDerivAt (fun t : ℝ => nilpotentDerivationFlow D hD t x) (D x) 0 := by
  have hnil := hD
  obtain ⟨k, hk⟩ := hnil
  have hk' : D.toLinearMap ^ (k + 2) = 0 := by rw [pow_add, hk, zero_mul]
  have hterm (i : ℕ) :
      HasDerivAt (fun t : ℝ => t ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x))
        (if i = 1 then D x else 0) 0 := by
    have hh : HasDerivAt
        (fun t : ℝ => t ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x))
        (((i : ℝ) * 0 ^ (i - 1)) • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow i).smul_const
        (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x)
    convert hh using 1
    by_cases hi : i = 1
    · subst i
      simp
    · by_cases hz : i = 0
      · subst i
        simp
      · have hsub : i - 1 ≠ 0 := by omega
        simp [hi, zero_pow hsub]
  have hsum := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.range (k + 2)) => hterm i)
  have heq : (fun t : ℝ => nilpotentDerivationFlow D hD t x) =
      (fun t => ∑ i ∈ Finset.range (k + 2),
        t ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x)) := by
    funext t
    exact nilpotentDerivationFlow_eq_sum D hD hk' t x
  rw [heq]
  simpa using hsum

end PolycyclicRecognition

end

end OAI
