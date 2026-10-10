import OAI.NumberTheory.Ostmann.Construction.PrimeExternalLogCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPrimeStatistic

namespace OAI

/-! # The original normalized moving amplitude and the proved prime statistic -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingPrimeCore {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (s : ℤ) (y : B → σ) (x z : ℝ) : ℂ :=
  (movingGiantPhase value outside small (bulkSlotLeaves n m slot) ggiant favorable s y x z *
    movingExternalRegularFactor value outside small (bulkSlotLeaves n m slot) greg s y x z) *
  movingFrequencyCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s
    (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulkSlotLeaves n m slot))
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊

/-- At prime points, the logarithmic coordinates and the positive-log
cutoffs agree with the original statistic on every rectangle. -/
theorem movingPrimeCore_interval_eq {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (gLeft gRight u v r w : ℝ) :
    primeExternalAverage ν (V n) u v r w (fun s y x z =>
      (φ (x - gLeft) : ℂ) * (φ (z - gRight) : ℂ) *
        movingPrimeCore q value outside μ childBound pivotBound V f g Dq S ψ X lo hi φ G
          n m small slot greg ggiant favorable
          s y (Real.log ⌊Real.exp x⌋₊) (Real.log ⌊Real.exp z⌋₊)) =
      movingOriginalPrimeStatistic q value outside μ ν childBound pivotBound V f g Dq S
        ψ X lo hi φ G n m small slot greg ggiant favorable gLeft gRight false u v r w := by
  unfold movingOriginalPrimeStatistic
  refine primeExternalAverage_congr_primes ν (V n) u v r w _ _ ?_
  intro s y p r hp hr
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr.pos
  simp only [movingPrimeCore, Real.exp_log hp', Real.exp_log hr', Nat.floor_natCast,
    giantOuterWeight, Bool.false_eq_true, ite_false, mul_one, positiveLogCutoff,
    hp', hr', ite_true]
  ring

/-- Exact identification of the two normalized giant priors with the
full-cell moving statistic. All normalizers and both phases remain present. -/
theorem movingPrimeCore_normalized_eq {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (gLeft gRight : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    smoothGiantExternalAverage ν (V n) φ gLeft gRight (fun s y p r =>
      movingPrimeCore q value outside μ childBound pivotBound V f g Dq S ψ X lo hi φ G
        n m small slot greg ggiant favorable s y (Real.log p) (Real.log r)) =
      (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange gLeft) φ gLeft +
        smoothGiantLogNormalizer (smoothGiantPrimeRange gRight) φ gRight) : ℂ) *
      movingOriginalPrimeStatistic q value outside μ ν childBound pivotBound V f g Dq S
        ψ X lo hi φ G n m small slot greg ggiant favorable gLeft gRight false
        (gLeft - 1) (gLeft + 1) (gRight - 1) (gRight + 1) := by
  rw [smoothGiantExternalAverage_log_cutoff ν (V n) φ gLeft gRight hout]
  apply congrArg (fun z : ℂ =>
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange gLeft) φ gLeft +
      smoothGiantLogNormalizer (smoothGiantPrimeRange gRight) φ gRight) : ℂ) * z)
  unfold movingOriginalPrimeStatistic
  refine primeExternalAverage_congr_primes ν (V n) (gLeft - 1) (gLeft + 1) (gRight - 1) (gRight + 1) _ _ ?_
  intro s y p r hp hr
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr.pos
  simp only [Real.exp_log hp', Real.exp_log hr', Nat.floor_natCast,
    movingPrimeCore, giantOuterWeight, Bool.false_eq_true, ite_false, mul_one]
  ring

end Ostmann

end OAI
