import OAI.NumberTheory.Ostmann.QuadraticSieveExponentIteration
import OAI.NumberTheory.Ostmann.QuadraticSieveInitialNorm

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem quadraticNorm_exponentBound_two :
    ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) 2 := by
  intro ε hε
  refine ⟨128,by norm_num,?_⟩
  intro M N hM hN
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hp : 1 ≤ ((M:ℝ)*N)^ε := Real.one_le_rpow
    (one_le_mul_of_one_le_of_one_le hM1 hN1) hε.le
  have he := quadraticNorm_initial_swapped M N hM hN
  rw [Real.rpow_two]
  refine he.trans ?_
  have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ (128:ℝ)*((M:ℝ)+(N:ℝ)^2) by positivity)
  nlinarith

theorem quadraticNorm_epsilon_of_improvement
    (himprove : ∀ ξ, 1 < ξ → ξ ≤ 2 →
      ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ →
      ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) (2-1/ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
      quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N) ≤
        C*((M:ℝ)*N)^ε*((M:ℝ)+N) :=
  epsilon_bound_of_exponent_improvement _ quadraticNorm_exponentBound_two himprove ε hε

end Ostmann.QuadraticSieve

end

end OAI
