import OAI.NumberTheory.EgyptianFractions.CyclicDiscrepancyAutomatic
import OAI.NumberTheory.EgyptianFractions.LeastResidueBridge

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Positive exponential cancellation supplies many small natural ceiling
remainders, with repetitions of the indexed numerators retained. -/
theorem ceiling_remainder_count_of_fourier {u : ℕ} [NeZero u]
    {Ω : Type*} [Fintype Ω] (A : Ω → ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * u)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ u)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, Complex.exp
        (2 * Real.pi * Complex.I * (l * A ω : ℕ) / (u : ℂ))‖ ≤
          (Fintype.card Ω : ℝ) * δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) < δ * u)).card : ℝ) := by
  classical
  have h := CyclicSmoothing.cyclic_small_interval_of_fourier
    (fun ω => -(A ω : ZMod u)) δ hδ hsmall hscale hdegree
    (fun l hl hld => by
      rw [norm_neg_residue_fourier_eq]
      exact hfourier l hl hld)
  simpa only [ceiling_remainder_eq_neg_cast_val] using h

/-- The same counting conclusion from normalized Fourier averages. -/
theorem ceiling_remainder_count_of_fourier_average {u : ℕ} [NeZero u]
    {Ω : Type*} [Fintype Ω] (A : Ω → ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * u)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ u)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖(∑ ω : Ω, Complex.exp
        (2 * Real.pi * Complex.I * (l * A ω : ℕ) / (u : ℂ))) /
          (Fintype.card Ω : ℂ)‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) < δ * u)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    apply ceiling_remainder_count_of_fourier A δ hδ hsmall hscale hdegree
    intro l hl hld
    have hf := hfourier l hl hld
    rw [norm_div, Complex.norm_natCast] at hf
    simpa only [mul_comm] using (div_le_iff₀ hN).mp hf

/-- Direct finite-average character interface for the random-product second
moment route; no conversion to real fractional parts is required. -/
theorem ceiling_remainder_count_of_character_expect {u : ℕ} [NeZero u]
    {Ω : Type*} [Fintype Ω] (A : Ω → ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * u)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ u)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖𝔼 ω : Ω, ZMod.stdAddChar ((l : ZMod u) * (A ω : ZMod u))‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) < δ * u)).card : ℝ) := by
  classical
  apply ceiling_remainder_count_of_fourier_average A δ hδ hsmall hscale hdegree
  intro l hl hld
  simpa only [Fintype.expect_eq_sum_div_card, stdAddChar_nat_product_phase] using
    hfourier l hl hld

/-- Cancellation forces its own modulus-size conditions, so the direct
ceiling-remainder count has no separate scale or degree hypothesis. -/
theorem ceiling_remainder_count_of_character_expect_automatic {u : ℕ} [NeZero u]
    {Ω : Type*} [Fintype Ω] (A : Ω → ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖𝔼 ω : Ω, ZMod.stdAddChar ((l : ZMod u) * (A ω : ZMod u))‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) < δ * u)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hc := CyclicSmoothing.cyclic_small_interval_of_fourier_automatic
      (fun ω => -(A ω : ZMod u)) δ hδ hsmall
      (fun l hl hld => by
        rw [norm_neg_residue_fourier_eq]
        have hf := hfourier l hl hld
        simp only [Fintype.expect_eq_sum_div_card, stdAddChar_nat_product_phase,
          norm_div, Complex.norm_natCast] at hf
        simpa only [mul_comm] using (div_le_iff₀ hN).mp hf)
    simpa only [ceiling_remainder_eq_neg_cast_val] using hc

end Problem337

end

end OAI
