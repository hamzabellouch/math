import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoBracketHeight

namespace OAI

section

noncomputable section
namespace InternalCatalan.ManuscriptSharpHeight
open Polynomial Set
open scoped BigOperators ComplexConjugate

private theorem quotient_norm_le {u d : ℂ} {D B : ℝ}
    (hu : ‖u‖ ≤ 1) (hD : 0 < D) (hd : D ≤ ‖d‖)
    (hB : 0 ≤ B) (hBD : 1 ≤ B * D) : ‖u / d‖ ≤ B := by
  rw [norm_div]
  apply (div_le_iff₀ (hD.trans_le hd)).mpr
  exact hu.trans (hBD.trans (mul_le_mul_of_nonneg_left hd hB))

private theorem numerator_norm_le {z r : ℂ} (hz : ‖z‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    ‖r * z‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul hr hz (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 1)

private theorem norm_map_sum_le {α : Type*} (tail : List α) (f : α → ℂ) (B : ℝ)
    (hb : ∀ a ∈ tail, ‖f a‖ ≤ B) : ‖(tail.map f).sum‖ ≤ (tail.length : ℝ) * B := by
  revert hb
  induction tail with
  | nil => intro _; simp
  | cons a tail ih =>
      intro hb
      have ha := hb a List.mem_cons_self
      have ht := ih (fun b h => hb b (List.mem_cons_of_mem _ h))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      exact (norm_add_le _ _).trans ((add_le_add ha ht).trans_eq (by ring))

theorem actual_tail_bounds {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierP2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re| ≤ (25000 / 9 : ℝ) ∧
    |(barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re| ≤ (1625 / 2 : ℝ) ∧
    |(barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re| ≤ (203125 / 4 : ℝ) := by
  have hp : ∀ zr ∈ barrierP2Tail,
      ‖zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x‖ ≤ (2500 / 9 : ℝ) := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierP2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (3 / 50 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd : (3 / 50 : ℝ) ^ 2 ≤ ‖barrierTailQuadraticDen zr.1 x‖ := by
      apply le_trans _ (Case2Height.quadratic_den_norm_lower hx hz1)
      nlinarith only [hgap, sq_nonneg (1 - ‖zr.1‖ - 3 / 50)]
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  have hvl : ∀ zr ∈ barrierV2Tail,
      ‖zr.2 * zr.1 / barrierTailLinearDen zr.1 x‖ ≤ (125 / 2 : ℝ) := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierV2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (2 / 125 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd := hgap.trans (Case2Height.linear_den_norm_lower hx (z := zr.1))
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  have hvq : ∀ zr ∈ barrierV2Tail,
      ‖zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x‖ ≤ (15625 / 4 : ℝ) := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierV2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (2 / 125 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd : (2 / 125 : ℝ) ^ 2 ≤ ‖barrierTailQuadraticDen zr.1 x‖ := by
      apply le_trans _ (Case2Height.quadratic_den_norm_lower hx hz1)
      nlinarith only [hgap, sq_nonneg (1 - ‖zr.1‖ - 2 / 125)]
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  constructor
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierP2Tail _ (2500 / 9) hp).trans_eq (by rw [barrier_tail_lengths.1]; norm_num))
  constructor
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierV2Tail _ (125 / 2) hvl).trans_eq (by rw [barrier_tail_lengths.2]; norm_num))
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierV2Tail _ (15625 / 4) hvq).trans_eq (by rw [barrier_tail_lengths.2]; norm_num))

private theorem abs_div_le_const {a b B : ℝ} (hb : 0 < |b|)
    (h : |a| ≤ B * |b|) : |a / b| ≤ B := by
  rw [abs_div]
  exact (div_le_iff₀ hb).mpr h

private theorem abs_sub_le_pair (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [Real.norm_eq_abs] using norm_sub_le a b

private theorem abs_four_sub_le (a b c d e : ℝ) :
    |a - b - c - d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_sub_le_pair a b
  have h2 := abs_sub_le_pair (a - b) c
  have h3 := abs_sub_le_pair (a - b - c) d
  have h4 := abs_sub_le_pair (a - b - c - d) e
  linarith

theorem X_formula_abs_lt {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |barrierCase2XDerivativeFormula x| < 12852 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  obtain ⟨hpu, _, hvp⟩ := Case2Height.actual_finite_bounds hx
  obtain ⟨hpt, hvt, _⟩ := actual_tail_bounds hx
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hd1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hA : |(19 / 48 : ℝ) / x| ≤ (11875 / 21 : ℝ) := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ (2500 / 21 : ℝ) := by
    apply abs_div_le_const (abs_pos.mpr hgpos.ne')
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |(65 / 24 : ℝ) * x / (1 + x ^ 2)| ≤ 3 := by
    apply abs_div_le_const (abs_pos.mpr hd.ne')
    rw [abs_mul, abs_of_pos hd]
    norm_num
    nlinarith
  have hD : |4 * ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierP2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)| ≤ (101980 / 9 : ℝ) := by
    rw [abs_mul]
    norm_num
    have hh := abs_add_le ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x)
      ((barrierP2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)
    linarith
  have hE : |(barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re| ≤ (1645 / 2 : ℝ) := by
    have hh := abs_add_le ((barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x)
      ((barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re)
    linarith
  unfold barrierCase2XDerivativeFormula
  exact (abs_four_sub_le _ _ _ _ _).trans_lt (by linarith)

theorem Y_formula_abs_lt {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |barrierCase2YDerivativeFormula x| < 102001 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  obtain ⟨_, hvu, _⟩ := Case2Height.actual_finite_bounds hx
  obtain ⟨_, _, hvt⟩ := actual_tail_bounds hx
  have hA : |(7 / 48 : ℝ) / x| ≤ (625 / 3 : ℝ) := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ (2500 / 21 : ℝ) := by
    apply abs_div_le_const (abs_pos.mpr hgpos.ne')
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |2 * ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)| ≤ (203345 / 2 : ℝ) := by
    rw [abs_mul]
    norm_num
    have hh := abs_add_le ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x)
      ((barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)
    linarith
  unfold barrierCase2YDerivativeFormula
  have hab := abs_sub_le_pair ((7 / 48 : ℝ) / x) ((1 / 12 : ℝ) / (1 - x))
  have habc := abs_add_le (((7 / 48 : ℝ) / x) - ((1 / 12 : ℝ) / (1 - x)))
    (2 * ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re))
  linarith

theorem actual_X_deriv_abs_lt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |deriv barrierCase2X x| < 12852 := by
  have h0 : x ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by norm_num) hxmargin)
  rw [(barrierCase2X_hasDerivAt hx h0).deriv]
  exact X_formula_abs_lt (abs_le.mpr ⟨hx.1.le, hx.2.le⟩) hxmargin hgap

theorem actual_Y_deriv_abs_lt {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |deriv barrierCase2Y x| < 102001 := by
  rw [(barrierCase2Y_hasDerivAt hx).deriv]
  exact Y_formula_abs_lt (abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩) hxmargin hgap

private theorem abs_five_sub_le (a b c d e g : ℝ) :
    |a - b - c - d - e - g| ≤ |a| + |b| + |c| + |d| + |e| + |g| := by
  have h1 := abs_four_sub_le a b c d e
  have h2 := abs_sub_le_pair (a - b - c - d - e) g
  linarith

theorem case1_X_deriv_abs_lt {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |deriv barrierCase1X x| < 12852 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  have h0 : x ≠ 0 := abs_pos.mp hxpos
  have h1 : x ≠ 1 := by intro h; subst x; norm_num at hgap
  obtain ⟨hpu, _, hvp⟩ := Case1Height.actual_finite_bounds hx
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hd1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hd2 : 1 ≤ (1 + x ^ 2) ^ 2 := by nlinarith [sq_nonneg (x ^ 2)]
  have hA : |(19 / 48 : ℝ) / x| ≤ (11875 / 21 : ℝ) := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ (2500 / 21 : ℝ) := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hgpos))
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |(41 / 24 : ℝ) * x / (1 + x ^ 2)| ≤ 2 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hd))
    rw [abs_mul, abs_of_pos hd]
    norm_num
    nlinarith
  have hD : |4 * barrierLambda1 * x / (1 + x ^ 2) ^ 2| ≤ 10 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt (sq_pos_of_pos hd)))
    rw [abs_mul, abs_of_pos (sq_pos_of_pos hd)]
    norm_num [barrierLambda1]
    nlinarith
  have hE : |2 * (barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 72 := by
    rw [abs_mul]
    norm_num
    linarith
  rw [(barrierCase1X_hasDerivAt h0 h1).deriv]
  unfold barrierCase1XDerivativeFormula
  exact (abs_five_sub_le _ _ _ _ _ _).trans_lt (by linarith)

theorem case1_Y_deriv_abs_lt {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |deriv barrierCase1Y x| < 102001 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  have h0 : x ≠ 0 := abs_pos.mp hxpos
  have h1 : x ≠ 1 := by intro h; subst x; norm_num at hgap
  obtain ⟨_, hvu, _⟩ := Case1Height.actual_finite_bounds hx
  have hA : |(7 / 48 : ℝ) / x| ≤ (625 / 3 : ℝ) := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ (2500 / 21 : ℝ) := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hgpos))
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |2 * (barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 72 := by
    rw [abs_mul]
    norm_num
    linarith
  rw [(barrierCase1Y_hasDerivAt h0 h1).deriv]
  unfold barrierCase1YDerivativeFormula
  have hab := abs_sub_le_pair ((7 / 48 : ℝ) / x) ((1 / 12 : ℝ) / (1 - x))
  have habc := abs_add_le (((7 / 48 : ℝ) / x) - ((1 / 12 : ℝ) / (1 - x)))
    (2 * (barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x)
  linarith

end InternalCatalan.ManuscriptSharpHeight

end

end

end OAI
