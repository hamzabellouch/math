import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedSmoothingNorm

namespace OAI

namespace Ostmann.QuadraticSieve

def SmoothingStepBound (ξ : ℝ) : Prop :=
  ∀ δ : ℝ, 0<δ → ∀ η : ℝ, 0<η → η≤δ/100 →
    ∃ C : ℝ, 0<C ∧ ∀ (M K N₀ D n : ℕ),
      0<M → 0<K → 0<N₀ → 0<D → 0<n → n≤N₀ → N₀≤M → K≤M →
      (2*(N₀:ℝ)^2/M)*((M:ℝ)*N₀)^η≤(K:ℝ) →
      Real.sqrt ((M:ℝ)/(K:ℝ))*N₀≤M →
      smoothingNorm M K (oddSquarefreeUpTo n) ≤
        C*((M:ℝ)*N₀)^δ*
          (smoothingNorm M K (oddSquarefreeUpTo (n/D))+
            (D:ℝ)^5*((M:ℝ)+Real.sqrt (M:ℝ)*(K:ℝ)^(ξ-1/2)))

end Ostmann.QuadraticSieve

end OAI
