import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalMatchedPatterns
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalDiagonalEnergy

namespace OAI

/-! # The full original correlation of two matched bulk assignments -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalMatchedCorrelation {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) : ℂ :=
  ∑ s : transferFrequencyRange (V n), ∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
      (movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk false))
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk true))
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
      movingExternalDiagonalWeight value outside small (bulk false) greg s.val φ Jleft Jright diagonal y x z))

theorem movingOriginalMatchedCorrelation_eq {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) :
    movingOriginalMatchedCorrelation q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n small bulk greg Jleft Jright diagonal u v r w center =
    ∑ s : transferFrequencyRange (V n), ∑ a : MovingDescendantFrequencyIndex V n,
      ∑ b : MovingDescendantFrequencyIndex V n,
        movingOriginalMatchedMean q value outside μ ν childBound pivotBound f g Dq S
          ψ X lo hi φ G n (fun side => if side then movingRootedFrequencyTree V n s.val b
            else movingRootedFrequencyTree V n s.val a)
          small bulk greg s.val Jleft Jright diagonal u v r w center := by
  unfold movingOriginalMatchedCorrelation
  apply Finset.sum_congr rfl
  intro s _
  have heq (y : B → σ) (x z : ℝ) :
      (movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk false))
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk true))
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) =
      ∑ a : MovingDescendantFrequencyIndex V n, ∑ b : MovingDescendantFrequencyIndex V n,
        movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (movingRootedFrequencyTree V n s.val a)
          (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk false))
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (movingRootedFrequencyTree V n s.val b)
          (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk true))
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) := by
    simp only [movingFrequencyCoefficient_original, star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [heq, Finset.sum_mul, complexIntegerInterval_sum, complexPrimeInterval_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  rfl

theorem movingOriginalMatchedMean_zero_frequency {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ)
    (side : Bool) (hzero : ¬ ∀ s ∈ allFrequencyList n (t side), s ≠ 0) :
    movingOriginalMatchedMean q value outside μ ν childBound pivotBound f g Dq S
      ψ X lo hi φ G n t small bulk greg sreg Jleft Jright diagonal u v r w center = 0 := by
  have hz := movingOriginalSampleAverage_zero_frequency q value outside μ childBound pivotBound
    (fun _ => f) (fun _ _ => hf) g Dq S ψ X lo hi φ G n (t side)
  unfold movingOriginalMatchedMean
  cases side <;>
    simp_rw [hz _ _ _ _ hzero] <;>
    simp only [star_zero, zero_mul, mul_zero, complexPrimeInterval, complexIntegerInterval,
      Finset.sum_const_zero, ite_self]

end Ostmann

end OAI
