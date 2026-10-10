import OAI.Probability.GammaPassage.RationalMean
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Positivity

namespace OAI

namespace GammaFPP
open PlanarFPP

lemma rationalLatticePoint_scale (x : Vertex) (n k : ℕ) (hk : 0 < k) :
    rationalLatticePoint (k • x) (k*n) = rationalLatticePoint x n := by
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  apply Prod.ext <;> simp [rationalLatticePoint, mul_div_mul_left, hkQ]

lemma rationalLatticePoint_add (x y : Vertex) (n : ℕ) :
    rationalLatticePoint (x+y) n = rationalLatticePoint x n + rationalLatticePoint y n := by
  ext <;> simp [rationalLatticePoint, add_div]

lemma rationalLatticePoint_neg (x : Vertex) (n : ℕ) :
    rationalLatticePoint (-x) n = -rationalLatticePoint x n := by
  ext <;> simp [rationalLatticePoint, neg_div]

/-- Simultaneous positive common denominator, without canonical-denominator
identities for addition or subtraction. -/
lemma rationalPair_common_denominator (q r : ℚ × ℚ) :
    ∃ n : ℕ, 0 < n ∧ ∃ x y : Vertex,
      q = rationalLatticePoint x n ∧ r = rationalLatticePoint y n := by
  let d := rationalDenominator q
  let e := rationalDenominator r
  refine ⟨e*d, Nat.mul_pos (rationalDenominator_pos r) (rationalDenominator_pos q),
    e • rationalNumerator q, d • rationalNumerator r, ?_, ?_⟩
  · rw [rationalLatticePoint_scale _ _ _ (rationalDenominator_pos r)]
    exact (rationalLatticePoint_numerator_denominator q).symm
  · rw [show e*d = d*e by exact Nat.mul_comm e d,
      rationalLatticePoint_scale _ _ _ (rationalDenominator_pos q)]
    exact (rationalLatticePoint_numerator_denominator r).symm

lemma rationalMean_zero (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (hzero : m 0 = 0) : rationalMean m 0 = 0 := by
  change rationalMean m (0, 0) = 0
  simpa [hzero] using rationalMean_integerPair m hn 0

lemma rationalMean_add_le (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (hadd : ∀ x y, m (x+y) ≤ m x+m y) (q r : ℚ × ℚ) :
    rationalMean m (q+r) ≤ rationalMean m q+rationalMean m r := by
  obtain ⟨n, hp, x, y, rfl, rfl⟩ := rationalPair_common_denominator q r
  rw [← rationalLatticePoint_add, rationalMean_rationalLatticePoint m hn _ _ hp,
    rationalMean_rationalLatticePoint m hn _ _ hp,
    rationalMean_rationalLatticePoint m hn _ _ hp, ← add_div]
  exact div_le_div_of_nonneg_right (hadd x y) (Nat.cast_nonneg n)

lemma rationalMean_neg (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (hneg : ∀ x, m (-x) = m x) (q : ℚ × ℚ) :
    rationalMean m (-q) = rationalMean m q := by
  have he := rationalLatticePoint_numerator_denominator q
  conv_lhs => rw [← he, ← rationalLatticePoint_neg]
  rw [rationalMean_rationalLatticePoint m hn _ _ (rationalDenominator_pos q), hneg]
  rfl

lemma rationalLatticePoint_rat_smul (a : ℚ) (x : Vertex) (n : ℕ) :
    rationalLatticePoint (a.num • x) (a.den*n) = a • rationalLatticePoint x n := by
  apply Prod.ext
  · change ((a.num • x.1 : ℤ) : ℚ)/((a.den*n : ℕ) : ℚ) =
      a*((x.1 : ℚ)/(n : ℚ))
    rw [zsmul_eq_mul, Int.cast_id, Int.cast_mul, Nat.cast_mul]
    calc
      _ = ((a.num : ℚ)/(a.den : ℚ))*((x.1 : ℚ)/(n : ℚ)) := by ring
      _ = _ := by rw [a.num_div_den]
  · change ((a.num • x.2 : ℤ) : ℚ)/((a.den*n : ℕ) : ℚ) =
      a*((x.2 : ℚ)/(n : ℚ))
    rw [zsmul_eq_mul, Int.cast_id, Int.cast_mul, Nat.cast_mul]
    calc
      _ = ((a.num : ℚ)/(a.den : ℚ))*((x.2 : ℚ)/(n : ℚ)) := by ring
      _ = _ := by rw [a.num_div_den]

/-- Signed rational scalars include zero; positivity is needed only for the
canonical denominator, never for the numerator. -/
lemma rationalMean_smul (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (hz : ∀ (k : ℤ) (x : Vertex), m (k • x) = (k.natAbs : ℝ)*m x)
    (a : ℚ) (q : ℚ × ℚ) :
    rationalMean m (a • q) = |(a : ℝ)| * rationalMean m q := by
  let d := rationalDenominator q
  let x := rationalNumerator q
  have hd : 0 < d := rationalDenominator_pos q
  have he : rationalLatticePoint x d = q := rationalLatticePoint_numerator_denominator q
  rw [← he, ← rationalLatticePoint_rat_smul,
    rationalMean_rationalLatticePoint m hn _ _ (Nat.mul_pos a.den_pos hd),
    rationalMean_rationalLatticePoint m hn _ _ hd, hz, Nat.cast_mul]
  have ha : |(a : ℝ)| = (a.num.natAbs : ℝ)/(a.den : ℝ) := by
    rw [Rat.cast_def, abs_div, abs_of_pos (show (0 : ℝ) < (a.den : ℝ) from Nat.cast_pos.mpr a.den_pos), Nat.cast_natAbs, Int.cast_abs]
  rw [ha]
  ring

/-- Exact L1 distance for a positive common denominator. -/
lemma rationalLatticePoint_real_l1 (x y : Vertex) (n : ℕ) (hn : 0 < n) :
    |((rationalLatticePoint x n).1 : ℝ)-((rationalLatticePoint y n).1 : ℝ)| +
      |((rationalLatticePoint x n).2 : ℝ)-((rationalLatticePoint y n).2 : ℝ)| =
      (((x.1-y.1).natAbs+(x.2-y.2).natAbs : ℕ) : ℝ)/(n : ℝ) := by
  simp only [rationalLatticePoint, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    ← sub_div, abs_div, abs_of_pos (show (0 : ℝ) < (n : ℝ) from Nat.cast_pos.mpr hn), Nat.cast_add,
    Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, add_div]

lemma rationalMean_l1 (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (C : ℝ)
    (hl : ∀ x y, |m x-m y| ≤ C *
      (((x.1-y.1).natAbs+(x.2-y.2).natAbs : ℕ) : ℝ))
    (q r : ℚ × ℚ) :
    |rationalMean m q-rationalMean m r| ≤ C *
      (|(q.1 : ℝ)-(r.1 : ℝ)|+|(q.2 : ℝ)-(r.2 : ℝ)|) := by
  obtain ⟨n, hp, x, y, rfl, rfl⟩ := rationalPair_common_denominator q r
  rw [rationalMean_rationalLatticePoint m hn _ _ hp,
    rationalMean_rationalLatticePoint m hn _ _ hp, ← sub_div, abs_div,
    abs_of_pos (show (0 : ℝ) < (n : ℝ) from Nat.cast_pos.mpr hp), rationalLatticePoint_real_l1 x y n hp]
  have hb := div_le_div_of_nonneg_right (hl x y) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [mul_div_assoc] using hb

end GammaFPP

end OAI
