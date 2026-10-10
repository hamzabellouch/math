import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedDiagonalEnergy
import OAI.NumberTheory.Ostmann.Characters.MixedExternalPartition

namespace OAI

/-! # Four unit rectangles for the original weighted diagonal energy -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedDiagonalEnergy_full_cell_bound {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small bulk : TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (H J center E : ℝ)
    (h : ∀ i j : Bool, ‖movingWeightedDiagonalEnergy q value outside μ ν
      childBound pivotBound V f g Dq S ψ X lo hi φ G n small bulk W
      (if i then H else H - 1) ((if i then H else H - 1) + 1)
      (if j then J else J - 1) ((if j then J else J - 1) + 1) center‖ ≤ E) :
    ‖movingWeightedDiagonalEnergy q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n small bulk W (H - 1) (H + 1) (J - 1) (J + 1) center‖ ≤ 4 * E := by
  exact mixedExternalAverage_full_cell_bound ν (V n) H J center E
    (fun s y x z =>
      (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) * W s y x z) h

end Ostmann

end OAI
