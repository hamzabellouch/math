import Mathlib
import OAI.Analysis.FreeWords.FullThroughLabel
import OAI.Analysis.FreeWords.VNAModel

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

universe u

local instance vnaOrder' {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (V : VonNeumannAlgebra H) : PartialOrder V.toStarSubalgebra :=
  CStarAlgebra.spectralOrder _

local instance vnaStarOrder' {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (V : VonNeumannAlgebra H) : StarOrderedRing V.toStarSubalgebra :=
  CStarAlgebra.spectralOrderedRing _

theorem concrete_free_words_through_label :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ N : ℕ, 1 ≤ N → ∃ d₀ : ℕ, N ≤ d₀ ∧
        ∀ d : ℕ, d₀ ≤ d →
          (∀ r : ℕ, 1 ≤ r → r ≤ N →
            ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
              (V : VonNeumannAlgebra H) (τ : V.toStarSubalgebra →ₚ[ℂ] ℂ),
              FaithfulTracial τ → NormalTrace V τ →
              ∀ (F : FreeMatrixCopies τ r d) (W : Sym (Fin d) r),
                ‖matrixWordSum V F W‖ ≤ KKThroughLabel.beta C d r W) ∧
          (∀ r : ℕ, 1 ≤ r → r ≤ N → ∀ a : Fin d,
            KKThroughLabel.throughSum C d r a ≤ 64) := by
  obtain ⟨C, hC, h⟩ := free_words_through_label.{u}
  refine ⟨C, hC, ?_⟩
  intro N hN
  obtain ⟨d₀, hd₀, hd⟩ := h N hN
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd'
  obtain ⟨hb, hs⟩ := hd d hd'
  refine ⟨?_, hs⟩
  intro r hr hrN H iG iI iC V τ hτ hNormal F W
  exact hb r hr hrN V.toStarSubalgebra τ hτ (F.toPartitions hτ) W

end

end KKFreeWords
end

end OAI
