import OAI.GroupTheory.Thompson.DyadicArithmetic
import OAI.GroupTheory.Thompson.BasicInterval
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace OAI

/-!
# Alignment of dyadic affine images with basic intervals

A slope which is an integer power of two sends every sufficiently fine grid
cell to a single grid cell, provided its dyadic translation has been absorbed
into the target denominator. The target depth can be made arbitrarily large.
-/

namespace ThompsonNonamenability

/-- An integer grid cell lying in the unit interval is a basic interval. -/
theorem basicInterval_of_integer_grid (d : ℕ) (j : ℤ)
    (h0 : 0 ≤ (j : ℝ) / (2 : ℝ) ^ d)
    (h1 : ((j : ℝ) + 1) / (2 : ℝ) ^ d ≤ 1) :
    ∃ I : BasicInterval, I.depth = d ∧
      I.left = (j : ℝ) / (2 : ℝ) ^ d ∧
      I.right = ((j : ℝ) + 1) / (2 : ℝ) ^ d := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  have hjr : (0 : ℝ) ≤ (j : ℝ) := by
    have hh := (le_div_iff₀ hp).1 h0
    simpa only [zero_mul] using hh
  have hj : (0 : ℤ) ≤ j := by exact_mod_cast hjr
  have hc : (j.toNat : ℝ) = (j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hj
  have hbound : j.toNat < 2 ^ d := by
    have hh : (j.toNat : ℝ) + 1 ≤ (2 : ℝ) ^ d := by
      rw [hc]
      exact (div_le_one hp).1 h1
    have hn : j.toNat + 1 ≤ 2 ^ d := by exact_mod_cast hh
    omega
  refine ⟨⟨d, ⟨j.toNat, hbound⟩⟩, rfl, ?_, ?_⟩
  · change (j.toNat : ℝ) / (2 : ℝ) ^ d = _
    rw [hc]
  · change ((j.toNat : ℝ) + 1) / (2 : ℝ) ^ d = _
    rw [hc]

/-- The target denominator simultaneously absorbs the translation and slope.
The freely specified lower bound on target depth gives arbitrarily small cells. -/
theorem dyadic_affine_aligned_denominators (q : ℤ) (b : ℝ)
    (hb : IsDyadic b) (L : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ d : ℕ, L ≤ d ∧
      (∃ j : ℤ, b = (j : ℝ) / (2 : ℝ) ^ d) ∧
      (2 : ℝ) ^ q / (2 : ℝ) ^ n = 1 / (2 : ℝ) ^ d := by
  obtain ⟨j, m, hj⟩ := hb
  cases q with
  | ofNat p =>
      refine ⟨m + L + p, ?_⟩
      intro n hn
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
      refine ⟨m + L + t, by omega, ?_, ?_⟩
      · exact dyadic_denominator_mono ⟨j, hj⟩ (by omega)
      · rw [Int.ofNat_eq_natCast, zpow_natCast]
        have he : m + L + p + t = p + (m + L + t) := by omega
        rw [he, pow_add]
        field_simp
  | negSucc p =>
      refine ⟨m + L, ?_⟩
      intro n hn
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
      refine ⟨m + L + t + (p + 1), by omega, ?_, ?_⟩
      · exact dyadic_denominator_mono ⟨j, hj⟩ (by omega)
      · rw [zpow_negSucc, pow_add]
        field_simp ; ring

/-- A single cell is aligned when the slope and translation share the target
grid denominator. No assumption about the source cell's location is needed. -/
theorem dyadic_affine_cell_of_denominator (q : ℤ) (b : ℝ) (n d : ℕ)
    (hb : ∃ j : ℤ, b = (j : ℝ) / (2 : ℝ) ^ d)
    (hs : (2 : ℝ) ^ q / (2 : ℝ) ^ n = 1 / (2 : ℝ) ^ d)
    (k : Fin (2 ^ n))
    (h0 : 0 ≤ (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b)
    (h1 : (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b ≤ 1) :
    ∃ I : BasicInterval, I.depth = d ∧
      I.left = (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b ∧
      I.right = (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b := by
  obtain ⟨j, hj⟩ := hb
  have hl : (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b =
      (((k.val : ℤ) + j : ℤ) : ℝ) / (2 : ℝ) ^ d := by
    calc
      _ = ((2 : ℝ) ^ q / (2 : ℝ) ^ n) * (k.val : ℝ) + b := by ring
      _ = (1 / (2 : ℝ) ^ d) * (k.val : ℝ) + (j : ℝ) / (2 : ℝ) ^ d := by
        rw [hs, hj]
      _ = _ := by push_cast; ring
  have hr : (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b =
      ((((k.val : ℤ) + j : ℤ) : ℝ) + 1) / (2 : ℝ) ^ d := by
    calc
      _ = ((2 : ℝ) ^ q / (2 : ℝ) ^ n) * ((k.val : ℝ) + 1) + b := by ring
      _ = (1 / (2 : ℝ) ^ d) * ((k.val : ℝ) + 1) + (j : ℝ) / (2 : ℝ) ^ d := by
        rw [hs, hj]
      _ = _ := by push_cast; ring
  obtain ⟨I, hd, hleft, hright⟩ := basicInterval_of_integer_grid d ((k.val : ℤ) + j)
    (hl ▸ h0) (hr ▸ h1)
  exact ⟨I, hd, hleft.trans hl.symm, hright.trans hr.symm⟩

/-- Every sufficiently fine cell has a basic interval as its dyadic affine
image whenever that image lies in `[0,1]`. -/
theorem dyadic_affine_grid_alignment (q : ℤ) (b : ℝ) (hb : IsDyadic b) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k : Fin (2 ^ n),
      0 ≤ (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b →
      (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b ≤ 1 →
      ∃ I : BasicInterval,
        I.left = (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b ∧
        I.right = (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b := by
  obtain ⟨N, hN⟩ := dyadic_affine_aligned_denominators q b hb 0
  refine ⟨N, ?_⟩
  intro n hn k h0 h1
  obtain ⟨d, _, hb', hs⟩ := hN n hn
  obtain ⟨I, _, hl, hr⟩ := dyadic_affine_cell_of_denominator q b n d hb' hs k h0 h1
  exact ⟨I, hl, hr⟩

/-- The affine image cells can simultaneously be required to have any prescribed
positive upper bound on their length. -/
theorem dyadic_affine_grid_alignment_small (q : ℤ) (b : ℝ) (hb : IsDyadic b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k : Fin (2 ^ n),
      0 ≤ (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b →
      (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b ≤ 1 →
      ∃ I : BasicInterval,
        I.left = (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b ∧
        I.right = (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b ∧
        I.length < ε := by
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hL' : 1 / (2 : ℝ) ^ L < ε := by
    simpa only [inv_pow, one_div] using hL
  obtain ⟨N, hN⟩ := dyadic_affine_aligned_denominators q b hb L
  refine ⟨N, ?_⟩
  intro n hn k h0 h1
  obtain ⟨d, hd, hb', hs⟩ := hN n hn
  obtain ⟨I, hdepth, hl, hr⟩ := dyadic_affine_cell_of_denominator q b n d hb' hs k h0 h1
  refine ⟨I, hl, hr, ?_⟩
  have hpow : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ d :=
    pow_le_pow_right₀ (by norm_num) hd
  have hle := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) L) hpow
  change ((2 : ℝ) ^ I.depth)⁻¹ < ε
  rw [hdepth, ← one_div]
  exact hle.trans_lt hL'

end ThompsonNonamenability

end OAI
