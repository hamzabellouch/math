import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedDiagonalMean
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalDiagonalEnergy

namespace OAI

/-! # Exact expansion of the coefficient square with its exterior mask retained -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingWeightedDiagonalEnergy {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small bulk : TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) : ℂ :=
  ∑ s : transferFrequencyRange (V n), ∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
      (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      W s.val y x z))

theorem movingWeightedDiagonalEnergy_eq {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small bulk : TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) :
    movingWeightedDiagonalEnergy q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n small bulk W u v r w center =
    ∑ s : transferFrequencyRange (V n), ∑ a : MovingDescendantFrequencyIndex V n,
      ∑ b : MovingDescendantFrequencyIndex V n,
        movingWeightedDiagonalMean q value outside μ ν childBound pivotBound f g Dq S
          ψ X lo hi φ G n (fun side => if side then movingRootedFrequencyTree V n s.val b
            else movingRootedFrequencyTree V n s.val a)
          small bulk (W s.val) u v r w center := by
  unfold movingWeightedDiagonalEnergy
  apply Finset.sum_congr rfl
  intro s _
  have heq (y : B → σ) (x z : ℝ) :
      (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) =
      ∑ a : MovingDescendantFrequencyIndex V n, ∑ b : MovingDescendantFrequencyIndex V n,
        movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (movingRootedFrequencyTree V n s.val a)
          (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (movingRootedFrequencyTree V n s.val b)
          (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) := by
    rw [movingFrequencyCoefficient_original, Complex.star_def, ← Complex.mul_conj']
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [heq, Finset.sum_mul, complexIntegerInterval_sum, complexPrimeInterval_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  rfl

end Ostmann

end OAI
