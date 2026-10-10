import OAI.NumberTheory.Ostmann.QuadraticSieveDyadicImprovementPrefix
import OAI.NumberTheory.Ostmann.QuadraticSieveSigned
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingDescent
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingStep

namespace OAI

namespace Ostmann.QuadraticSieve

theorem quadraticNorm_exponent_improvement (ξ : ℝ) (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ) :
    ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) (2-1/ξ) := by
  apply quadraticNorm_exponent_improvement_of_dyadic_recursive hξ1.le
  intro ε hε
  exact smoothingStepBound_dyadic_recursive hξ1 hξ2 hξ
    (smoothingStepBound_of_exponentBound hξ1 hξ2 hξ) ε hε

theorem heathBrown_quadraticNorm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U N : ℕ, 0 < U → 0 < N →
      quadraticNorm (oddSquarefreeUpTo U) (oddSquarefreeUpTo N) ≤
        C*((U : ℝ)*N)^ε*((U : ℝ)+N) :=
  quadraticNorm_epsilon_of_improvement quadraticNorm_exponent_improvement ε hε

theorem heathBrown_quadratic_large_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U N : ℕ, 0 < U → 0 < N →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N →
      jacobiEnergy (oddSquarefreeUpTo U) S a ≤
        C*((U : ℝ)*N)^ε*((U : ℝ)+N)*coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := heathBrown_quadraticNorm ε hε
  refine ⟨C,hC,?_⟩
  intro U N hU hN S a hS
  exact (jacobiEnergy_le_quadraticNorm _ _ _).trans
    (mul_le_mul_of_nonneg_right
      ((quadraticNorm_mono_columns _ hS).trans (hbound U N hU hN))
      (coefficientEnergy_nonneg S a))

theorem heathBrown_signed_quadratic_large_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U N : ℕ, 0 < U → 0 < N →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N →
      signedJacobiEnergy U S a ≤
        C*((U : ℝ)*N)^ε*((U : ℝ)+N)*coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := heathBrown_quadratic_large_sieve ε hε
  refine ⟨8*C,by positivity,?_⟩
  intro U N hU hN S a hS
  have hh := signedJacobiEnergy_le_of_unsigned U S a
    (fun n hn => (mem_oddSquarefreeUpTo.mp (hS hn)).2.2.1)
    (show 0 ≤ C*((U : ℝ)*N)^ε*((U : ℝ)+N) by positivity)
    (fun b => hbound U N hU hN S b hS)
  convert hh using 1
  ring

end Ostmann.QuadraticSieve

end OAI
