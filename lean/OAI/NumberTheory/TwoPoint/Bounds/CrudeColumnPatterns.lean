import OAI.NumberTheory.TwoPoint.Walks.ColumnRepresentatives
import OAI.NumberTheory.TwoPoint.Walks.ColumnHarmonicSum
import OAI.NumberTheory.TwoPoint.Walks.RankEnumeration

namespace OAI

/-! Complete column equality patterns have only one representative index per slot. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

abbrev CrudeColumnPatternCode (J R : ℕ) := Fin J → Fin R → Fin R

def decodeCrudeColumnPattern {J R : ℕ} (c : CrudeColumnPatternCode J R)
    (j : Fin J) (i k : Fin R) : Bool := decide (c j i = c j k)

theorem crude_column_pattern_cover {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) :
    ∃ c : CrudeColumnPatternCode J R, ∀ j i k,
      decodeCrudeColumnPattern c j i k = decide (w j i = w j k) := by
  refine ⟨fun j => columnRepresentative (w j) ∅, ?_⟩
  intro j i k
  exact decide_eq_decide.mpr (columnRepresentative_eq_iff (w j) ∅ i k)

lemma card_crudeColumnPatternCode (J R : ℕ) :
    Fintype.card (CrudeColumnPatternCode J R) = R ^ (R * J) := by
  simp only [CrudeColumnPatternCode, Fintype.card_fun, Fintype.card_fin, pow_mul]

theorem crude_column_pattern_count_bound (J R : ℕ) (L C : ℝ)
    (hL : 0 < L) (hJ : (J : ℝ) ≤ C * Real.log L)
    (hR : (R : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (CrudeColumnPatternCode J R) : ℝ) ≤
      Real.exp (2 * C * R * (Real.log L) ^ 2) := by
  have hlog : Real.log ((R : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < R + 1) hR
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogL : 0 ≤ Real.log L := by
    have hp : (1 : ℝ) ≤ L ^ (2 : ℕ) := (by linarith : (1 : ℝ) ≤ R + 1).trans hR
    have hone : 1 ≤ L := by nlinarith
    exact Real.log_nonneg hone
  rw [card_crudeColumnPatternCode]
  push_cast
  calc
    _ ≤ ((R : ℝ) + 1) ^ (R * J) := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = Real.exp (((R * J : ℕ) : ℝ) * Real.log ((R : ℝ) + 1)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < R + 1)]
    _ ≤ Real.exp (((R * J : ℕ) : ℝ) * (2 * Real.log L)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (by positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 2 * R * Real.log L by positivity)
      push_cast
      nlinarith

end TwoPointCorrelations

end OAI
