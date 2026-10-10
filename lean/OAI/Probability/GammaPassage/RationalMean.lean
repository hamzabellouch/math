import OAI.Probability.FirstPassage.Paths
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP
open PlanarFPP

/-- A rational pair represented by one positive natural denominator. -/
def rationalLatticePoint (x : Vertex) (n : ℕ) : ℚ × ℚ :=
  ((x.1 : ℚ) / (n : ℚ), (x.2 : ℚ) / (n : ℚ))

def rationalDenominator (q : ℚ × ℚ) : ℕ := q.1.den * q.2.den

def rationalNumerator (q : ℚ × ℚ) : Vertex :=
  (q.1.num * (q.2.den : ℤ), q.2.num * (q.1.den : ℤ))

theorem rationalDenominator_pos (q : ℚ × ℚ) : 0 < rationalDenominator q :=
  Nat.mul_pos q.1.den_pos q.2.den_pos

/-- Explicit common-denominator representation, including zero coordinates. -/
theorem rationalLatticePoint_numerator_denominator (q : ℚ × ℚ) :
    rationalLatticePoint (rationalNumerator q) (rationalDenominator q) = q := by
  have h₁ : (q.1.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.1.den_ne_zero
  have h₂ : (q.2.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.2.den_ne_zero
  apply Prod.ext
  · change ((q.1.num * (q.2.den : ℤ) : ℤ) : ℚ) /
      ((q.1.den * q.2.den : ℕ) : ℚ) = q.1
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    calc
      _ = (q.1.num : ℚ) / (q.1.den : ℚ) := by field_simp
      _ = q.1 := q.1.num_div_den
  · change ((q.2.num * (q.1.den : ℤ) : ℤ) : ℚ) /
      ((q.1.den * q.2.den : ℕ) : ℚ) = q.2
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    calc
      _ = (q.2.num : ℚ) / (q.2.den : ℚ) := by field_simp
      _ = q.2 := q.2.num_div_den

/-- Equality of rational points yields equality after integer cross multiplication. -/
theorem rationalLatticePoint_cross {x y : Vertex} {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k)
    (he : rationalLatticePoint x n = rationalLatticePoint y k) :
    k • x = n • y := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hx := (div_eq_div_iff hnQ hkQ).mp (congrArg Prod.fst he)
  have hy := (div_eq_div_iff hnQ hkQ).mp (congrArg Prod.snd he)
  have hxZ : x.1 * (k : ℤ) = y.1 * (n : ℤ) := by exact_mod_cast hx
  have hyZ : x.2 * (k : ℤ) = y.2 * (n : ℤ) := by exact_mod_cast hy
  apply Prod.ext
  · change k • x.1 = n • y.1
    simpa only [nsmul_eq_mul, mul_comm] using hxZ
  · change k • x.2 = n • y.2
    simpa only [nsmul_eq_mul, mul_comm] using hyZ

/-- Denominator compatibility derived from homogeneity, not assumed as a premise. -/
theorem latticeMean_div_eq_of_cross (m : Vertex → ℝ)
    (hm : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ) * m x)
    {x y : Vertex} {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (he : k • x = n • y) : m x / (n : ℝ) = m y / (k : ℝ) := by
  have h := congrArg m he
  rw [hm, hm] at h
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))).mpr
  simpa only [mul_comm] using h

/-- A concrete rational mean; no representative is chosen nonconstructively. -/
noncomputable def rationalMean (m : Vertex → ℝ) (q : ℚ × ℚ) : ℝ :=
  m (rationalNumerator q) / (rationalDenominator q : ℝ)

/-- Evaluation at every integer pair over every positive natural denominator. -/
theorem rationalMean_rationalLatticePoint (m : Vertex → ℝ)
    (hm : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ) * m x)
    (x : Vertex) (n : ℕ) (hn : 0 < n) :
    rationalMean m (rationalLatticePoint x n) = m x / (n : ℝ) := by
  let q := rationalLatticePoint x n
  have he : rationalLatticePoint (rationalNumerator q) (rationalDenominator q) =
      rationalLatticePoint x n := rationalLatticePoint_numerator_denominator q
  exact latticeMean_div_eq_of_cross m hm (rationalDenominator_pos q) hn
    (rationalLatticePoint_cross (rationalDenominator_pos q) hn he)

/-- Literal agreement with the integer lattice (denominator one). -/
theorem rationalMean_integerPair (m : Vertex → ℝ)
    (hm : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ) * m x)
    (x : Vertex) : rationalMean m ((x.1 : ℚ), (x.2 : ℚ)) = m x := by
  simpa [rationalLatticePoint] using rationalMean_rationalLatticePoint m hm x 1 (by decide)

end GammaFPP

end OAI
