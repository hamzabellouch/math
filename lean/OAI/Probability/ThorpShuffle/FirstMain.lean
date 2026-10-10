import OAI.Probability.ThorpShuffle.FirstFourier

namespace OAI

universe uE

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Filter Topology

theorem first_reciprocal_main :
    (BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) ∧
    (∀ n : ℕ, 1 ≤ n → reciprocalFirst n ≤ C1) ∧
    Tendsto exceptionalFirst atTop (nhds 0)) ∧
    (∀ (d : ℕ) (_hd : 3 ≤ d)
    (e : Position d ≃ Fin 8 × Fin (2 ^ (d - 3)))
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (Equiv.Perm (Position d)) E)
    [Representation.IsIrreducible ρ]
    (_ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ν : Equiv.Perm (Position d) → ℝ)
    (_ : ∀ g, 0 ≤ ν g) (_ : ∑ g, ν g = 1)
    (_ : ∀ (i : Fin 8) (g : Equiv.Perm (Position d)),
      ∑ h : Equiv.Perm (Fin (2 ^ (d - 3))),
          ν (g * Block.embedding e (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin (2 ^ (d - 3)))) : ℝ) /
          Fintype.card (Equiv.Perm (Position d))),
    ‖LinearMap.toContinuousLinearMap (Fourier.integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ)) := by
  exact ⟨reciprocal_degrees, eight_block_fourier_bound⟩

end Thorp.Current

end

end OAI
