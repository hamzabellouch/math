import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Energy.BarrierFinitePotentialRat

namespace OAI

noncomputable section

namespace InternalCatalan

section
open scoped BigOperators

def manuscriptTailMoment (tail : List (ℂ × ℂ)) (k : ℕ) : ℂ :=
  (tail.map (fun zr => zr.2 * zr.1 ^ k)).sum

def manuscriptTailLogPair (xs ys : List (ℂ × ℂ)) : ℂ :=
  (xs.map (fun zr => (ys.map (fun ws =>
    zr.2 * ws.2 * Complex.log (1 - zr.1 * ws.1))).sum)).sum

theorem manuscript_tail_pair_hasSum (z r w s : ℂ)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ =>
      (r * z ^ (k + 1)) * (s * w ^ (k + 1)) / ((k + 1 : ℕ) : ℂ))
      (-(r * s * Complex.log (1 - z * w))) := by
  have hzw : ‖z * w‖ < 1 := by
    rw [norm_mul]
    calc
      ‖z‖ * ‖w‖ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hw.le (norm_nonneg z)
      _ < 1 := by simpa only [mul_one] using hz
  convert (Complex.hasSum_taylorSeries_neg_log' hzw).mul_left (r * s) using 1
  · funext k
    simp only [mul_pow, Nat.cast_add, Nat.cast_one]
    ring
  · ring

private theorem manuscript_tail_row_hasSum (z r : ℂ) (hz : ‖z‖ < 1)
    (ys : List (ℂ × ℂ)) (hy : ∀ ws ∈ ys, ‖ws.1‖ < 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)) * manuscriptTailMoment ys (k + 1) /
      ((k + 1 : ℕ) : ℂ))
      (-(ys.map (fun ws => r * ws.2 * Complex.log (1 - z * ws.1))).sum) := by
  induction ys with
  | nil => simp [manuscriptTailMoment]
  | cons ws ys ih =>
    have hr := manuscript_tail_pair_hasSum z r ws.1 ws.2 hz (hy ws List.mem_cons_self)
    have ht := ih (fun v hv => hy v (List.mem_cons_of_mem _ hv))
    simpa only [manuscriptTailMoment, List.map_cons, List.sum_cons,
      mul_add, add_div, neg_add] using hr.add ht

theorem manuscript_tail_bilinear_hasSum (xs ys : List (ℂ × ℂ))
    (hx : ∀ zr ∈ xs, ‖zr.1‖ < 1) (hy : ∀ ws ∈ ys, ‖ws.1‖ < 1) :
    HasSum (fun k : ℕ => manuscriptTailMoment xs (k + 1) *
      manuscriptTailMoment ys (k + 1) / ((k + 1 : ℕ) : ℂ))
      (-manuscriptTailLogPair xs ys) := by
  induction xs with
  | nil => simp [manuscriptTailMoment, manuscriptTailLogPair]
  | cons zr xs ih =>
    have hr := manuscript_tail_row_hasSum zr.1 zr.2 (hx zr List.mem_cons_self) ys hy
    have ht := ih (fun v hv => hx v (List.mem_cons_of_mem _ hv))
    simpa only [manuscriptTailMoment, manuscriptTailLogPair, List.map_cons,
      List.sum_cons, add_mul, add_div, neg_add] using hr.add ht

theorem manuscript_tail_square_hasSum (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1)
    (hreal : ∀ k : ℕ, (manuscriptTailMoment tail (k + 1)).im = 0) :
    HasSum (fun k : ℕ => (manuscriptTailMoment tail (k + 1)).re ^ 2 /
      ((k + 1 : ℕ) : ℝ)) (-(manuscriptTailLogPair tail tail).re) := by
  have h := Complex.hasSum_re (manuscript_tail_bilinear_hasSum tail tail htail htail)
  have he (k : ℕ) :
      (manuscriptTailMoment tail (k + 1) * manuscriptTailMoment tail (k + 1)).re =
        (manuscriptTailMoment tail (k + 1)).re ^ 2 := by
    rw [Complex.mul_re, hreal k]
    ring
  simpa only [Complex.div_natCast_re, Complex.neg_re, he] using h

end

def manuscriptNormLogRow (ys : List (ℂ × ℂ)) (zr : ℂ × ℂ) : ℝ :=
  (ys.map (fun ws =>
    (- (zr.2 * ws.2) * Complex.log (1 - zr.1 * ws.1)).re)).sum

theorem manuscript_norm_log_row_eq (ys : List (ℂ × ℂ)) (zr : ℂ × ℂ) :
    -((ys.map (fun ws => zr.2 * ws.2 * Complex.log (1 - zr.1 * ws.1))).sum).re =
      manuscriptNormLogRow ys zr := by
  induction ys with
  | nil => simp [manuscriptNormLogRow]
  | cons ws ys ih =>
    simpa only [manuscriptNormLogRow, List.map_cons, List.sum_cons,
      Complex.add_re, neg_add, neg_mul, Complex.neg_re] using
      congrArg (fun x => -(zr.2 * ws.2 * Complex.log (1 - zr.1 * ws.1)).re + x) ih

theorem manuscript_norm_log_sum_eq (xs ys : List (ℂ × ℂ)) :
    -(manuscriptTailLogPair xs ys).re =
      (xs.map (manuscriptNormLogRow ys)).sum := by
  induction xs with
  | nil => simp [manuscriptTailLogPair]
  | cons zr xs ih =>
    simpa only [manuscriptTailLogPair, List.map_cons, List.sum_cons,
      Complex.add_re, neg_add, manuscript_norm_log_row_eq] using
      congrArg (fun x => manuscriptNormLogRow ys zr + x) ih

open scoped BigOperators

theorem manuscriptTrialNormSq_eq_finite_log (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1)
    (hreal : ∀ k : ℕ, (manuscriptTailMoment tail (k + 1)).im = 0) :
    barrierTrialNormSq (barrierTrial cs tail) =
      (∑ k ∈ Finset.range cs.length,
        (((cs.getD k 0 : ℝ) / 100000000) ^ 2 +
          2 * ((cs.getD k 0 : ℝ) / 100000000) * (manuscriptTailMoment tail (k + 1)).re) /
            ((k + 1 : ℕ) : ℝ)) - (manuscriptTailLogPair tail tail).re := by
  have hf : HasSum (fun k : ℕ =>
      (((cs.getD k 0 : ℝ) / 100000000) ^ 2 +
        2 * ((cs.getD k 0 : ℝ) / 100000000) * (manuscriptTailMoment tail (k + 1)).re) /
          ((k + 1 : ℕ) : ℝ))
      (∑ k ∈ Finset.range cs.length,
        (((cs.getD k 0 : ℝ) / 100000000) ^ 2 +
          2 * ((cs.getD k 0 : ℝ) / 100000000) * (manuscriptTailMoment tail (k + 1)).re) /
            ((k + 1 : ℕ) : ℝ)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  have ht := manuscript_tail_square_hasSum tail htail hreal
  have hactual : HasSum (fun k : ℕ => barrierTrial cs tail (k + 1) ^ 2 /
      ((k + 1 : ℕ) : ℝ))
      ((∑ k ∈ Finset.range cs.length,
        (((cs.getD k 0 : ℝ) / 100000000) ^ 2 +
          2 * ((cs.getD k 0 : ℝ) / 100000000) * (manuscriptTailMoment tail (k + 1)).re) /
            ((k + 1 : ℕ) : ℝ)) - (manuscriptTailLogPair tail tail).re) := by
    convert hf.add ht using 1
    · funext k
      simp [barrierTrial, barrierFiniteCoeff, manuscriptTailMoment]
      ring
  exact hactual.tsum_eq

theorem manuscript_conjugate_tail_moment_im (z r : ℂ) (k : ℕ) :
    (manuscriptTailMoment (barrierConjugatePair z r) k).im = 0 := by
  have h : star r * star z ^ k = star (r * z ^ k) := by simp
  simp only [manuscriptTailMoment, barrierConjugatePair, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [h]
  simp only [Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel]

private theorem manuscript_real_tail_moment_im (a c : ℚ) (k : ℕ) :
    (manuscriptTailMoment [(barrierComplex a 0, barrierComplex c 0)] k).im = 0 := by
  simp only [manuscriptTailMoment, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [barrierComplex_real_pow]
  simp only [barrierComplex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Rat.cast_zero, mul_zero, zero_mul, zero_add]

private theorem manuscript_tail_moment_append (xs ys : List (ℂ × ℂ)) (k : ℕ) :
    manuscriptTailMoment (xs ++ ys) k = manuscriptTailMoment xs k +
      manuscriptTailMoment ys k := by
  simp only [manuscriptTailMoment, List.map_append, List.sum_append]

theorem manuscriptP2_tail_moment_im (k : ℕ) :
    (manuscriptTailMoment barrierP2Tail k).im = 0 := by
  simp only [barrierP2Tail, manuscript_tail_moment_append, Complex.add_im,
    manuscript_conjugate_tail_moment_im, manuscript_real_tail_moment_im, add_zero]

theorem manuscriptV2_tail_moment_im (k : ℕ) :
    (manuscriptTailMoment barrierV2Tail k).im = 0 := by
  simp only [barrierV2Tail, manuscript_tail_moment_append, Complex.add_im,
    manuscript_conjugate_tail_moment_im, manuscript_real_tail_moment_im, add_zero]

theorem manuscriptP2_norm_log_formula :
    barrierTrialNormSq barrierP2 =
      (∑ k ∈ Finset.range barrierP2Finite.length,
        (((barrierP2Finite.getD k 0 : ℝ) / 100000000) ^ 2 +
          2 * ((barrierP2Finite.getD k 0 : ℝ) / 100000000) *
            (manuscriptTailMoment barrierP2Tail (k + 1)).re) / ((k + 1 : ℕ) : ℝ)) -
        (manuscriptTailLogPair barrierP2Tail barrierP2Tail).re := by
  apply manuscriptTrialNormSq_eq_finite_log
  · intro zr hzr
    exact lt_of_le_of_lt (barrierP2_tail_norm_bounds zr hzr).1 (by norm_num)
  · intro k
    exact manuscriptP2_tail_moment_im (k + 1)

theorem manuscriptV2_norm_log_formula :
    barrierTrialNormSq barrierV2 =
      (∑ k ∈ Finset.range barrierV2Finite.length,
        (((barrierV2Finite.getD k 0 : ℝ) / 100000000) ^ 2 +
          2 * ((barrierV2Finite.getD k 0 : ℝ) / 100000000) *
            (manuscriptTailMoment barrierV2Tail (k + 1)).re) / ((k + 1 : ℕ) : ℝ)) -
        (manuscriptTailLogPair barrierV2Tail barrierV2Tail).re := by
  apply manuscriptTrialNormSq_eq_finite_log
  · intro zr hzr
    exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)
  · intro k
    exact manuscriptV2_tail_moment_im (k + 1)

open scoped BigOperators

theorem manuscript_tail_log_pair_im (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1)
    (hreal : ∀ k : ℕ, (manuscriptTailMoment tail (k + 1)).im = 0) :
    (manuscriptTailLogPair tail tail).im = 0 := by
  have h := Complex.hasSum_im (manuscript_tail_bilinear_hasSum tail tail htail htail)
  have hz : HasSum (fun _ : ℕ => (0 : ℝ)) (-(manuscriptTailLogPair tail tail).im) := by
    simpa only [Complex.div_natCast_im, Complex.mul_im, hreal, mul_zero,
      zero_mul, zero_add, zero_div, Complex.neg_im] using h
  have he := (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).unique hz
  linarith

theorem manuscriptP2_double_log_im :
    (manuscriptTailLogPair barrierP2Tail barrierP2Tail).im = 0 := by
  apply manuscript_tail_log_pair_im
  · intro zr hzr
    exact lt_of_le_of_lt (barrierP2_tail_norm_bounds zr hzr).1 (by norm_num)
  · intro k
    exact manuscriptP2_tail_moment_im (k + 1)

theorem manuscriptV2_double_log_im :
    (manuscriptTailLogPair barrierV2Tail barrierV2Tail).im = 0 := by
  apply manuscript_tail_log_pair_im
  · intro zr hzr
    exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)
  · intro k
    exact manuscriptV2_tail_moment_im (k + 1)

theorem manuscriptTrialNormSq_complex_log_formula
    (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1)
    (hreal : ∀ k : ℕ, (manuscriptTailMoment tail (k + 1)).im = 0) :
    ((barrierTrialNormSq (barrierTrial cs tail) : ℝ) : ℂ) =
      (((∑ k ∈ Finset.range cs.length,
        (((cs.getD k 0 : ℝ) / 100000000) ^ 2 +
          2 * ((cs.getD k 0 : ℝ) / 100000000) * (manuscriptTailMoment tail (k + 1)).re) /
            ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) - manuscriptTailLogPair tail tail := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re, Complex.sub_re] using
      manuscriptTrialNormSq_eq_finite_log cs tail htail hreal
  · simp only [Complex.ofReal_im, Complex.sub_im,
      manuscript_tail_log_pair_im tail htail hreal, sub_zero]

end InternalCatalan

end

end OAI
