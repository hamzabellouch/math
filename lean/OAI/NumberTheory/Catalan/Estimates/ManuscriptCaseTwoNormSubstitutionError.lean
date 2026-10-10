import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow00
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow01
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow02
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow03
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow04
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow05
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow06
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow07
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow08
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogPRow09
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow00
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow01
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow02
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow03
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow04
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow05
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow06
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow07
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow08
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow09
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow10
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow11
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormLogVRow12
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow00
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow01
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow02
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow03
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow04
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow05
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow06
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow07
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow08
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingPRow09
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow00
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow01
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow02
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow03
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow04
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow05
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow06
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow07
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow08
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow09
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow10
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow11
import OAI.NumberTheory.Catalan.Determinants.ManuscriptNormRoundingVRow12

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptRatComplexMul (z w : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

def manuscriptRatComplexPow (z : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => manuscriptRatComplexMul (manuscriptRatComplexPow z n) z

theorem manuscript_rat_complex_mul (z w : ℚ × ℚ) :
    barrierComplex (manuscriptRatComplexMul z w).1 (manuscriptRatComplexMul z w).2 =
      barrierComplex z.1 z.2 * barrierComplex w.1 w.2 := by
  apply Complex.ext <;>
    simp [manuscriptRatComplexMul, barrierComplex, Complex.mul_re, Complex.mul_im]

theorem manuscript_rat_complex_pow (z : ℚ × ℚ) (k : ℕ) :
    barrierComplex (manuscriptRatComplexPow z k).1 (manuscriptRatComplexPow z k).2 =
      (barrierComplex z.1 z.2) ^ k := by
  induction k with
  | zero => apply Complex.ext <;> simp [manuscriptRatComplexPow, barrierComplex]
  | succ k ih =>
    rw [manuscriptRatComplexPow, manuscript_rat_complex_mul, ih, pow_succ]

def manuscriptRatTail (rs : List (ℚ × ℚ)) (ps : List BarrierRationalPairRow) :
    List ((ℚ × ℚ) × (ℚ × ℚ)) :=
  rs.map (fun ac => ((ac.1, 0), (ac.2, 0))) ++
    ps.flatMap (fun row =>
      [((row.a, row.b), (row.c, row.d)), ((row.a, -row.b), (row.c, -row.d))])

noncomputable def manuscriptRatTailCast (xs : List ((ℚ × ℚ) × (ℚ × ℚ))) :
    List (ℂ × ℂ) :=
  xs.map (fun zr => (barrierComplex zr.1.1 zr.1.2, barrierComplex zr.2.1 zr.2.2))

private theorem manuscript_barrier_complex_conj (a b : ℚ) :
    barrierComplex a (-b) = star (barrierComplex a b) := by
  apply Complex.ext <;> simp [barrierComplex]

private theorem manuscript_rat_tail_cast (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) :
    manuscriptRatTailCast (manuscriptRatTail rs ps) =
      barrierExpandRealRows rs ++ barrierExpandPairRows ps := by
  simp only [manuscriptRatTailCast, manuscriptRatTail, List.map_append, List.map_map]
  apply congrArg (fun rest : List (ℂ × ℂ) => barrierExpandRealRows rs ++ rest)
  induction ps with
  | nil => rfl
  | cons row ps ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
      barrierExpandPairRows, barrierExpandPairRow, barrierConjugatePair,
      manuscript_barrier_complex_conj] at *
    exact congrArg (fun rest =>
      [(barrierComplex row.a row.b, barrierComplex row.c row.d),
       (star (barrierComplex row.a row.b), star (barrierComplex row.c row.d))] ++ rest) ih

def manuscriptP2RatTail := manuscriptRatTail barrierP2RealRows barrierP2PairRows
def manuscriptV2RatTail := manuscriptRatTail barrierV2RealRows barrierV2PairRows

theorem manuscriptP2_rat_tail_cast : manuscriptRatTailCast manuscriptP2RatTail = barrierP2Tail := by
  rw [manuscriptP2RatTail, manuscript_rat_tail_cast, barrierP2Tail_eq_grouped]

theorem manuscriptV2_rat_tail_cast : manuscriptRatTailCast manuscriptV2RatTail = barrierV2Tail := by
  rw [manuscriptV2RatTail, manuscript_rat_tail_cast, barrierV2Tail_eq_grouped]

def manuscriptRatTailMomentRe (xs : List ((ℚ × ℚ) × (ℚ × ℚ))) (k : ℕ) : ℚ :=
  (xs.map (fun zr => (manuscriptRatComplexMul zr.2 (manuscriptRatComplexPow zr.1 k)).1)).sum

theorem manuscript_rat_tail_moment_re (xs : List ((ℚ × ℚ) × (ℚ × ℚ))) (k : ℕ) :
    (manuscriptTailMoment (manuscriptRatTailCast xs) k).re =
      (manuscriptRatTailMomentRe xs k : ℝ) := by
  induction xs with
  | nil => simp [manuscriptTailMoment, manuscriptRatTailCast, manuscriptRatTailMomentRe]
  | cons zr xs ih =>
    simp only [manuscriptTailMoment, manuscriptRatTailCast, manuscriptRatTailMomentRe,
      List.map_cons, List.sum_cons, Complex.add_re, Rat.cast_add] at *
    rw [ih, ← manuscript_rat_complex_pow, ← manuscript_rat_complex_mul]
    rfl

def manuscriptRatFiniteCross (cs : List ℤ) (xs : List ((ℚ × ℚ) × (ℚ × ℚ))) : ℚ :=
  ∑ k ∈ Finset.range cs.length,
    (((cs.getD k 0 : ℚ) / 100000000) ^ 2 +
      2 * ((cs.getD k 0 : ℚ) / 100000000) * manuscriptRatTailMomentRe xs (k + 1)) /
        ((k + 1 : ℕ) : ℚ)

theorem manuscript_rat_finite_cross_cast (cs : List ℤ)
    (xs : List ((ℚ × ℚ) × (ℚ × ℚ))) :
    (∑ k ∈ Finset.range cs.length,
      (((cs.getD k 0 : ℝ) / 100000000) ^ 2 +
        2 * ((cs.getD k 0 : ℝ) / 100000000) *
          (manuscriptTailMoment (manuscriptRatTailCast xs) (k + 1)).re) /
            ((k + 1 : ℕ) : ℝ)) = (manuscriptRatFiniteCross cs xs : ℝ) := by
  simp only [manuscriptRatFiniteCross, Rat.cast_sum, Rat.cast_div, Rat.cast_add,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast, Rat.cast_natCast,
    Rat.cast_ofNat, manuscript_rat_tail_moment_re]

end InternalCatalan

end

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptCase1NormSubstituteRat : ℚ :=
  manuscriptRatFiniteCross barrierP1Finite [] +
    (1 / 2 : ℚ) * manuscriptRatFiniteCross barrierV1Finite []

theorem manuscript_case1_norm_substitute_eq_finite :
    manuscriptCase1NormSubstituteRat =
      (∑ k ∈ Finset.range barrierP1Finite.length,
        ((barrierP1Finite.getD k 0 : ℚ) / 100000000) ^ 2 / ((k + 1 : ℕ) : ℚ)) +
      (1 / 2 : ℚ) * (∑ k ∈ Finset.range barrierV1Finite.length,
        ((barrierV1Finite.getD k 0 : ℚ) / 100000000) ^ 2 / ((k + 1 : ℕ) : ℚ)) := by
  simp only [manuscriptCase1NormSubstituteRat, manuscriptRatFiniteCross,
    manuscriptRatTailMomentRe, List.map_nil, List.sum_nil, mul_zero, add_zero]

theorem manuscript_case1_norm_substitute_cutoff :
    manuscriptCase1NormSubstituteRat < (93205 / 100000 : ℚ) := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan
open scoped BigOperators

theorem manuscriptP2_rat_finite_cross :
    manuscriptRatFiniteCross barrierP2Finite manuscriptP2RatTail =
      (-296928319732106451627960687431479625954222369 / 3076171875000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem manuscriptP2_finite_cross :
    (∑ k ∈ Finset.range barrierP2Finite.length,
      (((barrierP2Finite.getD k 0 : ℝ) / 100000000) ^ 2 +
        2 * ((barrierP2Finite.getD k 0 : ℝ) / 100000000) *
          (manuscriptTailMoment barrierP2Tail (k + 1)).re) /
            ((k + 1 : ℕ) : ℝ)) = (-296928319732106451627960687431479625954222369 / 3076171875000000000000000000000000000000000000 : ℝ) := by
  have h := manuscript_rat_finite_cross_cast barrierP2Finite manuscriptP2RatTail
  rw [manuscriptP2_rat_tail_cast, manuscriptP2_rat_finite_cross] at h
  simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using h

theorem manuscriptV2_rat_finite_cross :
    manuscriptRatFiniteCross barrierV2Finite manuscriptV2RatTail =
      (6146480006200710712347154932018199794871098631 / 12500000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

theorem manuscriptV2_finite_cross :
    (∑ k ∈ Finset.range barrierV2Finite.length,
      (((barrierV2Finite.getD k 0 : ℝ) / 100000000) ^ 2 +
        2 * ((barrierV2Finite.getD k 0 : ℝ) / 100000000) *
          (manuscriptTailMoment barrierV2Tail (k + 1)).re) /
            ((k + 1 : ℕ) : ℝ)) = (6146480006200710712347154932018199794871098631 / 12500000000000000000000000000000000000000000000 : ℝ) := by
  have h := manuscript_rat_finite_cross_cast barrierV2Finite manuscriptV2RatTail
  rw [manuscriptV2_rat_tail_cast, manuscriptV2_rat_finite_cross] at h
  simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using h

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan

def manuscriptCase1NormRoundedSubstituteRat : ℚ :=
  manuscriptRatFiniteCross barrierP1Finite [] +
    (1 / 2 : ℚ) * manuscriptRatFiniteCross barrierV1Finite []

theorem manuscript_case1_norm_rounded_substitute_eq :
    manuscriptCase1NormSubstituteRat = manuscriptCase1NormRoundedSubstituteRat := by
  rfl

theorem manuscript_case1_norm_added_rounding_error_zero :
    |(manuscriptCase1NormSubstituteRat : ℝ) -
      (manuscriptCase1NormRoundedSubstituteRat : ℝ)| = 0 := by
  rw [manuscript_case1_norm_rounded_substitute_eq]
  simp only [sub_self, abs_zero]

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem manuscript_case1_norm_eq_substitute :
    barrierTrialNormSq barrierP1 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV1 =
      (manuscriptCase1NormSubstituteRat : ℝ) := by
  change barrierTrialNormSq (barrierTrial barrierP1Finite []) +
    (1 / 2 : ℝ) * barrierTrialNormSq (barrierTrial barrierV1Finite []) = _
  rw [barrierTrialNormSq_nil_eq_sum, barrierTrialNormSq_nil_eq_sum,
    manuscript_case1_norm_substitute_eq_finite]
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_sum, Rat.cast_pow, Rat.cast_intCast, Rat.cast_natCast]

theorem manuscript_case1_norm_substitution_error_zero :
    |(barrierTrialNormSq barrierP1 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV1) -
      (manuscriptCase1NormSubstituteRat : ℝ)| = 0 := by
  rw [manuscript_case1_norm_eq_substitute, sub_self, abs_zero]

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscriptP2_negative_double_log_upper :
    -(manuscriptTailLogPair barrierP2Tail barrierP2Tail).re ≤ ((162821182950024005659017087707 / 1000000000000000000000000000000) : ℝ) := by
  rw [manuscript_norm_log_sum_eq]
  change (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 0 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 1 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 2 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 3 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 4 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 5 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 6 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 7 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 8 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 9 (0, 0)) + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormPRow0_upper, manuscriptNormPRow1_upper, manuscriptNormPRow2_upper, manuscriptNormPRow3_upper, manuscriptNormPRow4_upper, manuscriptNormPRow5_upper, manuscriptNormPRow6_upper, manuscriptNormPRow7_upper, manuscriptNormPRow8_upper, manuscriptNormPRow9_upper]

theorem manuscriptV2_negative_double_log_upper :
    -(manuscriptTailLogPair barrierV2Tail barrierV2Tail).re ≤ ((49995618680088529056431008857 / 62500000000000000000000000000) : ℝ) := by
  rw [manuscript_norm_log_sum_eq]
  change (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 0 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 1 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 2 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 3 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 4 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 5 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 6 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 7 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 8 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 9 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 10 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 11 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 12 (0, 0)) + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormVRow0_upper, manuscriptNormVRow1_upper, manuscriptNormVRow2_upper, manuscriptNormVRow3_upper, manuscriptNormVRow4_upper, manuscriptNormVRow5_upper, manuscriptNormVRow6_upper, manuscriptNormVRow7_upper, manuscriptNormVRow8_upper, manuscriptNormVRow9_upper, manuscriptNormVRow10_upper, manuscriptNormVRow11_upper, manuscriptNormVRow12_upper]

theorem manuscript_case2_norm_sharp_upper :
    2 * barrierTrialNormSq barrierP2 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV2 <
      ((194603994071 / 250000000000) : ℝ) := by
  have hq : 2 * ((-296928319732106451627960687431479625954222369 / 3076171875000000000000000000000000000000000000) + (162821182950024005659017087707 / 1000000000000000000000000000000)) + (1 / 2 : ℚ) * ((6146480006200710712347154932018199794871098631 / 12500000000000000000000000000000000000000000000) + (49995618680088529056431008857 / 62500000000000000000000000000)) < (194603994071 / 250000000000) := by
    decide +kernel
  have hr := (Rat.cast_lt (K := ℝ)).mpr hq
  push_cast at hr
  rw [manuscriptP2_norm_log_formula, manuscriptV2_norm_log_formula,
    manuscriptP2_finite_cross, manuscriptV2_finite_cross]
  linarith only [hr, manuscriptP2_negative_double_log_upper,
    manuscriptV2_negative_double_log_upper]

end InternalCatalan

end

end

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormPSubstituteRat : ℚ :=
  manuscriptNormPSubstituteRow0 +
    manuscriptNormPSubstituteRow1 +
    manuscriptNormPSubstituteRow2 +
    manuscriptNormPSubstituteRow3 +
    manuscriptNormPSubstituteRow4 +
    manuscriptNormPSubstituteRow5 +
    manuscriptNormPSubstituteRow6 +
    manuscriptNormPSubstituteRow7 +
    manuscriptNormPSubstituteRow8 +
    manuscriptNormPSubstituteRow9

theorem manuscriptNormPSubstituteRat_upper : manuscriptNormPSubstituteRat ≤ (162821182950024005659017087707 / 1000000000000000000000000000000) := by
  unfold manuscriptNormPSubstituteRat
  linarith only [manuscriptNormPSubstituteRow0_upper,
    manuscriptNormPSubstituteRow1_upper,
    manuscriptNormPSubstituteRow2_upper,
    manuscriptNormPSubstituteRow3_upper,
    manuscriptNormPSubstituteRow4_upper,
    manuscriptNormPSubstituteRow5_upper,
    manuscriptNormPSubstituteRow6_upper,
    manuscriptNormPSubstituteRow7_upper,
    manuscriptNormPSubstituteRow8_upper,
    manuscriptNormPSubstituteRow9_upper]

def manuscriptNormVSubstituteRat : ℚ :=
  manuscriptNormVSubstituteRow0 +
    manuscriptNormVSubstituteRow1 +
    manuscriptNormVSubstituteRow2 +
    manuscriptNormVSubstituteRow3 +
    manuscriptNormVSubstituteRow4 +
    manuscriptNormVSubstituteRow5 +
    manuscriptNormVSubstituteRow6 +
    manuscriptNormVSubstituteRow7 +
    manuscriptNormVSubstituteRow8 +
    manuscriptNormVSubstituteRow9 +
    manuscriptNormVSubstituteRow10 +
    manuscriptNormVSubstituteRow11 +
    manuscriptNormVSubstituteRow12

theorem manuscriptNormVSubstituteRat_upper : manuscriptNormVSubstituteRat ≤ (49995618680088529056431008857 / 62500000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRat
  linarith only [manuscriptNormVSubstituteRow0_upper,
    manuscriptNormVSubstituteRow1_upper,
    manuscriptNormVSubstituteRow2_upper,
    manuscriptNormVSubstituteRow3_upper,
    manuscriptNormVSubstituteRow4_upper,
    manuscriptNormVSubstituteRow5_upper,
    manuscriptNormVSubstituteRow6_upper,
    manuscriptNormVSubstituteRow7_upper,
    manuscriptNormVSubstituteRow8_upper,
    manuscriptNormVSubstituteRow9_upper,
    manuscriptNormVSubstituteRow10_upper,
    manuscriptNormVSubstituteRow11_upper,
    manuscriptNormVSubstituteRow12_upper]

def manuscriptCase2NormSubstituteRat : ℚ :=
  2 * (manuscriptRatFiniteCross barrierP2Finite manuscriptP2RatTail +
    manuscriptNormPSubstituteRat) +
  (1 / 2 : ℚ) * (manuscriptRatFiniteCross barrierV2Finite manuscriptV2RatTail +
    manuscriptNormVSubstituteRat)

theorem manuscript_case2_norm_substitute_cutoff :
    manuscriptCase2NormSubstituteRat < (77843 / 100000 : ℚ) := by
  have hr : 2 * ((-296928319732106451627960687431479625954222369 / 3076171875000000000000000000000000000000000000) + (162821182950024005659017087707 / 1000000000000000000000000000000)) +
      (1 / 2 : ℚ) * ((6146480006200710712347154932018199794871098631 / 12500000000000000000000000000000000000000000000) + (49995618680088529056431008857 / 62500000000000000000000000000)) <
        (77843 / 100000 : ℚ) := by
    decide +kernel
  unfold manuscriptCase2NormSubstituteRat
  rw [manuscriptP2_rat_finite_cross, manuscriptV2_rat_finite_cross]
  linarith only [hr, manuscriptNormPSubstituteRat_upper, manuscriptNormVSubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem manuscriptNormPComposition_error :
    |-(manuscriptTailLogPair barrierP2Tail barrierP2Tail).re -
      (manuscriptNormPSubstituteRat : ℝ)| ≤ (((497429312937 / 100000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormPCompositionRow0_error
  have h1 := manuscriptNormPCompositionRow1_error
  have h2 := manuscriptNormPCompositionRow2_error
  have h3 := manuscriptNormPCompositionRow3_error
  have h4 := manuscriptNormPCompositionRow4_error
  have h5 := manuscriptNormPCompositionRow5_error
  have h6 := manuscriptNormPCompositionRow6_error
  have h7 := manuscriptNormPCompositionRow7_error
  have h8 := manuscriptNormPCompositionRow8_error
  have h9 := manuscriptNormPCompositionRow9_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [manuscript_norm_log_sum_eq]
  change |(manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 0 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 1 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 2 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 3 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 4 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 5 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 6 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 7 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 8 (0, 0)) + (manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 9 (0, 0)) + (0 : ℝ))))))))))) - (manuscriptNormPSubstituteRat : ℝ)| ≤ _
  unfold manuscriptNormPSubstituteRat
  push_cast
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2]

theorem manuscriptNormVComposition_error :
    |-(manuscriptTailLogPair barrierV2Tail barrierV2Tail).re -
      (manuscriptNormVSubstituteRat : ℝ)| ≤ (((14491782799067 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormVCompositionRow0_error
  have h1 := manuscriptNormVCompositionRow1_error
  have h2 := manuscriptNormVCompositionRow2_error
  have h3 := manuscriptNormVCompositionRow3_error
  have h4 := manuscriptNormVCompositionRow4_error
  have h5 := manuscriptNormVCompositionRow5_error
  have h6 := manuscriptNormVCompositionRow6_error
  have h7 := manuscriptNormVCompositionRow7_error
  have h8 := manuscriptNormVCompositionRow8_error
  have h9 := manuscriptNormVCompositionRow9_error
  have h10 := manuscriptNormVCompositionRow10_error
  have h11 := manuscriptNormVCompositionRow11_error
  have h12 := manuscriptNormVCompositionRow12_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [manuscript_norm_log_sum_eq]
  change |(manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 0 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 1 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 2 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 3 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 4 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 5 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 6 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 7 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 8 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 9 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 10 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 11 (0, 0)) + (manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 12 (0, 0)) + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRat : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRat
  push_cast
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1,
    (abs_le.mp h10).1,
    (abs_le.mp h11).1,
    (abs_le.mp h12).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2,
    (abs_le.mp h10).2,
    (abs_le.mp h11).2,
    (abs_le.mp h12).2]

private theorem manuscript_case2_norm_composition_difference :
    (2 * barrierTrialNormSq barrierP2 +
      (1 / 2 : ℝ) * barrierTrialNormSq barrierV2) -
      (manuscriptCase2NormSubstituteRat : ℝ) =
    2 * (-(manuscriptTailLogPair barrierP2Tail barrierP2Tail).re -
      (manuscriptNormPSubstituteRat : ℝ)) +
    (1 / 2 : ℝ) * (-(manuscriptTailLogPair barrierV2Tail barrierV2Tail).re -
      (manuscriptNormVSubstituteRat : ℝ)) := by
  have hP := manuscript_rat_finite_cross_cast barrierP2Finite manuscriptP2RatTail
  rw [manuscriptP2_rat_tail_cast] at hP
  have hV := manuscript_rat_finite_cross_cast barrierV2Finite manuscriptV2RatTail
  rw [manuscriptV2_rat_tail_cast] at hV
  rw [manuscriptP2_norm_log_formula, manuscriptV2_norm_log_formula, hP, hV]
  simp only [manuscriptCase2NormSubstituteRat, Rat.cast_add, Rat.cast_mul,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  ring

theorem manuscript_case2_norm_substitution_error :
    |(2 * barrierTrialNormSq barrierP2 +
      (1 / 2 : ℝ) * barrierTrialNormSq barrierV2) -
      (manuscriptCase2NormSubstituteRat : ℝ)| <
        (285 / 1000000000000000 : ℝ) := by
  have hP := manuscriptNormPComposition_error
  have hV := manuscriptNormVComposition_error
  have hbq : 2 * (497429312937 / 100000000000000000000000000000) + (1 / 2 : ℚ) * (14491782799067 / 500000000000000000000000000000) <
      (285 / 1000000000000000 : ℚ) := by
    decide +kernel
  have hb := (Rat.cast_lt (K := ℝ)).mpr hbq
  push_cast at hP hV hb
  rw [manuscript_case2_norm_composition_difference]
  apply abs_lt.mpr
  constructor
  · linarith only [(abs_le.mp hP).1, (abs_le.mp hV).1, hb]
  · linarith only [(abs_le.mp hP).2, (abs_le.mp hV).2, hb]

end InternalCatalan

end

end

end OAI
