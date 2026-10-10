import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W13

variable {K : Type*} [Field K] [Algebra ℚ K]

def omegaCoefficients (a b : K) : Fin 4 → K := ![1, 1 / a, -(1 / b), -(1 / (a * b))]

theorem rationalIndependent_mul {ι : Type*} {v : ι → K}
    (hv : LinearIndependent ℚ v) {s : K} (hs : s ≠ 0) :
    LinearIndependent ℚ (fun i => s * v i) := by
  exact hv.map_injOn (LinearMap.mulLeft ℚ s)
    (fun _ _ _ _ h => mul_left_cancel₀ hs h)

theorem rationalIndependent_signedReverse {a b : K}
    (h : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K)) :
    LinearIndependent ℚ (![a * b, b, -a, -1] : Fin 4 → K) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro r hr
  have hz : ∑ i : Fin 4, (![ -(r 3), -(r 2), r 1, r 0] : Fin 4 → ℚ) i •
      (![1, a, b, a * b] : Fin 4 → K) i = 0 := by
    convert hr using 1
    simp [Fin.sum_univ_succ, Algebra.smul_def]
    ring
  have hh := h _ hz
  intro i
  fin_cases i
  · simpa using hh 3
  · simpa using hh 2
  · simpa using hh 1
  · simpa using hh 0

omit [Algebra ℚ K] in
theorem mul_omegaCoefficients {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (fun i => (a * b) * omegaCoefficients a b i) = ![a * b, b, -a, -1] := by
  funext i
  fin_cases i <;> simp [omegaCoefficients] <;> field_simp [ha, hb]

theorem rationalIndependent_omegaCoefficients {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K)) :
    LinearIndependent ℚ (omegaCoefficients a b) := by
  have hc := rationalIndependent_mul (rationalIndependent_signedReverse h)
    (inv_ne_zero (mul_ne_zero ha hb))
  convert hc using 1
  funext i
  fin_cases i <;> simp [omegaCoefficients] <;> field_simp [ha, hb]

end WeightedTorusJets.W13

end

end SiegelZeros

end OAI
