import OAI.Combinatorics.EditApproximation.Geometry.ActualRoundedGroupInputs

namespace OAI

namespace EditApproximation

/-- Every envelope queried by a shared group bounds both endpoint loops,
including the fractional-envelope, unit-spacing case. -/
theorem groupRoundSpacing_endpoint_counts (M b exponent : ℕ) (h : ℚ)
    (hM : 0 < M) (_hh : 0 ≤ h) (hfloor : (b : ℚ) / M ≤ h) :
    2 * (12 * b) / groupRoundSpacing exponent h + 2 ≤ 24 * 2 ^ exponent * M + 2 ∧
    2 * ⌈2 * h⌉₊ / groupRoundSpacing exponent h + 2 ≤ 4 * 2 ^ exponent + 4 := by
  let K := 2 ^ exponent
  let g := groupRoundSpacing exponent h
  have hg : 0 < g := groupRoundSpacing_pos exponent h
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hspacing : h ≤ (K : ℚ) * g := by
    simpa only [K, Nat.cast_pow, Nat.cast_ofNat] using groupRoundSpacing_envelope_bound exponent h
  have hb : (b : ℚ) ≤ M * h := by
    nlinarith only [(div_le_iff₀ hMr).mp hfloor]
  have hbN : b ≤ K * M * g := by
    have hx := mul_le_mul_of_nonneg_left hspacing (Nat.cast_nonneg M)
    have hr : (b : ℚ) ≤ ((K * M * g : ℕ) : ℚ) := by push_cast; nlinarith only [hb, hx]
    exact_mod_cast hr
  have hfirst : 2 * (12 * b) / g ≤ 24 * K * M := by
    have hd := Nat.div_mul_le_self (2 * (12 * b)) g
    have hn : 2 * (12 * b) ≤ (24 * K * M) * g := by nlinarith only [Nat.mul_le_mul_left 24 hbN]
    nlinarith only [hd, hn, hg]
  have hceil : ⌈2 * h⌉₊ ≤ 2 * K * g + 1 := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith only [hspacing]
  have hsecond : 2 * ⌈2 * h⌉₊ / g ≤ 4 * K + 2 := by
    have hd := Nat.div_mul_le_self (2 * ⌈2 * h⌉₊) g
    have hn : 2 * ⌈2 * h⌉₊ ≤ (4 * K + 2) * g := by
      nlinarith only [hceil, hg]
    nlinarith only [hd, hn, hg]
  exact ⟨Nat.add_le_add_right hfirst 2, by simpa only [K, g, Nat.add_assoc, Nat.reduceAdd] using Nat.add_le_add_right hsecond 2⟩

end EditApproximation

end OAI
