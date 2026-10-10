import OAI.NumberTheory.Ostmann.Arithmetic.MovingFirstProductBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationProductBounds

namespace OAI

/-! # Concrete product caps for the first two integer extensions -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

private theorem ceiling_exp_double (E : ℝ) (hE : 0 ≤ E) :
    (⌈Real.exp E⌉₊ : ℝ) ≤ 2 * Real.exp E := by
  have h := (Nat.ceil_lt_add_one (Real.exp_pos E).le).le
  have he := Real.one_le_exp hE
  linarith

theorem first_two_cell_caps (T₀ T₁ E W : ℝ) (hE : 0 ≤ E)
    (hW : W ≤ Real.exp (T₀ + E)) :
    W ≤ Real.exp T₀ * (⌈Real.exp E⌉₊ : ℝ) ∧
      ((⌈Real.exp E⌉₊ ^ 2 : ℕ) : ℝ) ≤
        Real.exp T₁ * (⌈Real.exp (2 * E - T₁ + Real.log 4)⌉₊ : ℝ) := by
  constructor
  · apply hW.trans
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil (Real.exp E)) (Real.exp_nonneg _)
  · have hc := ceiling_exp_double E hE
    have hs := mul_self_le_mul_self (Nat.cast_nonneg ⌈Real.exp E⌉₊) hc
    have hce := Nat.le_ceil (Real.exp (2 * E - T₁ + Real.log 4))
    calc
      _ ≤ (2 * Real.exp E) ^ 2 := by simpa only [Nat.cast_pow, pow_two, Nat.cast_mul] using hs
      _ = Real.exp T₁ * Real.exp (2 * E - T₁ + Real.log 4) := by
        rw [← Real.exp_add]
        have heq : T₁ + (2 * E - T₁ + Real.log 4) = 2 * E + Real.log 4 := by ring
        rw [heq, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4),
          show 2 * E = E + E by ring, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hce (Real.exp_nonneg _)

theorem movingCompensation_pivot_lower_of_bound {σ : Type*} (value : σ → ℕ)
    (μ : σ → ℝ) (c G : ℝ)
    (hlower : ∀ x, μ x ≠ 0 → Real.exp (c - 1) ≤ (value x : ℝ))
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior μ n a ≠ 0) (p : ℕ)
    (hp : Real.exp (G - 1) ≤ (p : ℝ)) :
    Real.exp (G - 1 + ((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) ≤
      (p * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℕ) := by
  rw [Real.exp_add]
  simpa only [Nat.cast_mul] using
    mul_le_mul hp (movingCompensation_product_lower value μ c hlower n a ha)
      (Real.exp_nonneg _) (Nat.cast_nonneg _)

theorem movingFrequencyCoefficient_initial_cell_cap {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi c E : ℝ) (hX : 0 < X) (hE : 0 ≤ E)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (hμ : ∀ x, μ 0 x ≠ 0 → Real.exp (c - 1) ≤ (value x : ℝ))
    (hwindow : X * hi ≤ Real.exp (G 1 - 1 + 4 * (c - 1) + E))
    (a : Fin 4 → σ) (ha : movingCompensationPrior (μ 0) 0 a ≠ 0)
    (s : ℤ) (small bulk : List σ) (p XR : ℕ)
    (hp : 0 < p) (hpbound : Real.exp (G 1 - 1) ≤ (p : ℝ))
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 0 s
      (List.ofFn a ++ small) bulk p XR ≠ 0) :
    XR * MovingSlotReversal.naturalProduct value (small ++ bulk) ≤ ⌈Real.exp E⌉₊ := by
  have hlow := movingCompensation_pivot_lower_of_bound value (μ 0) c (G 1) hμ 0 a ha p hpbound
  have hU := movingCompensation_product_lower value (μ 0) c hμ 0 a ha
  have hUp : 0 < MovingSlotReversal.naturalProduct value (List.ofFn a) := by
    have hpos := (Real.exp_pos _).trans_le hU
    exact_mod_cast hpos
  have hc := (first_two_cell_caps (G 1 - 1 + 4 * (c - 1)) 0 E (X * hi) hE hwindow).1
  exact movingFrequencyCoefficient_initial_retained_bound value outside μ childBound pivotBound V
    q F g Dq S ψ X lo hi (Real.exp (G 1 - 1 + 4 * (c - 1))) hX φ G s
    (List.ofFn a) small bulk p XR ⌈Real.exp E⌉₊ hp hUp (by simpa only [flattenMovingSlots, movingCompensationSlots, Nat.pow_zero, one_mul, Nat.cast_ofNat] using hlow) hc h

theorem movingFrequencyCoefficient_one_cell_cap {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi c₀ c₁ E : ℝ) (hX : 0 < X) (hE : 0 ≤ E)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμ₀ : ∀ x, μ 0 x ≠ 0 → Real.exp (c₀ - 1) ≤ (value x : ℝ))
    (hμ₁ : ∀ x, μ 1 x ≠ 0 → Real.exp (c₁ - 1) ≤ (value x : ℝ))
    (hwindow : X * hi ≤ Real.exp (G 1 - 1 + 4 * (c₀ - 1) + E))
    (a : (Fin 4 → σ) × (Fin 4 → σ)) (ha : movingCompensationPrior (μ 1) 1 a ≠ 0)
    (s : ℤ) (small bulk : List σ × List σ) (p XR : ℕ)
    (hp : 0 < p) (hpbound : Real.exp (G 2 - 1) ≤ (p : ℝ))
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 1 s
      (List.ofFn a.1 ++ small.1, List.ofFn a.2 ++ small.2) bulk p XR ≠ 0) :
    XR * MovingSlotReversal.naturalProduct value
      ((small.1 ++ bulk.1) ++ (small.2 ++ bulk.2)) ≤
        ⌈Real.exp (2 * E - (G 2 - 1 + 8 * (c₁ - 1)) + Real.log 4)⌉₊ := by
  let T₀ := G 1 - 1 + 4 * (c₀ - 1)
  let T₁ := G 2 - 1 + 8 * (c₁ - 1)
  have hlow := movingCompensation_pivot_lower_of_bound value (μ 1) c₁ (G 2) hμ₁ 1 a ha p hpbound
  have hU := movingCompensation_product_lower value (μ 1) c₁ hμ₁ 1 a ha
  have hUp : 0 < MovingSlotReversal.naturalProduct value (List.ofFn a.1 ++ List.ofFn a.2) := by
    have hpos := (Real.exp_pos _).trans_le hU
    exact_mod_cast hpos
  have hmin (b : Fin 4 → σ) (hb : movingCompensationPrior (μ 0) 0 b ≠ 0)
      (p' : ℕ) (hp' : 0 < p') (hφ' : φ (Real.log p' - G 1) ≠ 0) :
      Real.exp T₀ ≤ (p' * MovingSlotReversal.naturalProduct value (List.ofFn b) : ℕ) := by
    have hlow' := movingInsertedPivot_product_lower value (μ 0) c₀ (G 1) φ hμ₀ hout 0 b hb p' hp' hφ'
    simpa only [T₀, flattenMovingSlots, movingCompensationSlots, Nat.pow_zero, one_mul,
      Nat.cast_ofNat] using hlow'
  have hcaps := first_two_cell_caps T₀ T₁ E (X * hi) hE hwindow
  apply movingFrequencyCoefficient_one_retained_bound value outside μ childBound pivotBound V
    q F g Dq S ψ X lo hi (Real.exp T₀) hX φ G hmin ⌈Real.exp E⌉₊ hcaps.1 s
    (List.ofFn a.1, List.ofFn a.2) small bulk p XR _ hp hUp (Real.exp T₁) _ hcaps.2 h
  simpa only [T₁, flattenMovingSlots, movingCompensationSlots, Nat.reducePow, Nat.reduceMul,
    Nat.cast_ofNat] using hlow

end Ostmann

end OAI
