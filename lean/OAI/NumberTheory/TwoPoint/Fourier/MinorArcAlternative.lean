import OAI.NumberTheory.TwoPoint.Fourier.MinorArcApproximation
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTheorem

namespace OAI

/-! The rational approximation used for the major/minor arc alternative,
with its actual short-window denominator cutoff. -/

namespace TwoPointCorrelations

lemma minor_arc_short_rational_approximation (α : ℝ) (H : ℕ) (W : ℝ)
    (hW : 0 < W) (hWH : W ≤ H) :
    ∃ (r : ℤ) (q : ℕ), 0 < q ∧ (q : ℝ) ≤ (H : ℝ) / W ∧
      IsCoprime (q : ℤ) r ∧
      |α - (r : ℝ) / q| ≤ W / ((H : ℝ) * q) ∧
      |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  let Q : ℕ := ⌊(H : ℝ) / W⌋₊
  have hQ : 0 < Q := Nat.floor_pos.mpr ((le_div_iff₀ hW).mpr (by simpa using hWH))
  obtain ⟨r, q, hq, hqQ, hcop, happ, hsquare⟩ := minor_arc_rational_approximation α Q hQ
  have hcut : (q : ℝ) ≤ (H : ℝ) / W :=
    (by exact_mod_cast hqQ : (q : ℝ) ≤ Q).trans (Nat.floor_le (by positivity))
  have hH : (0 : ℝ) < H := hW.trans_le hWH
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hQlarge : (H : ℝ) ≤ ((Q : ℝ) + 1) * W :=
    (div_le_iff₀ hW).mp (Nat.lt_floor_add_one ((H : ℝ) / W)).le
  refine ⟨r, q, hq, hcut, hcop, happ.trans ?_, hsquare⟩
  apply (div_le_div_iff₀ (mul_pos hQ0 hq0) (mul_pos hH hq0)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hQlarge hq0.le]

end TwoPointCorrelations

end OAI
