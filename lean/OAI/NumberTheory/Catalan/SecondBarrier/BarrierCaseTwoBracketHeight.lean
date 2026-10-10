import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneBracketHeight
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction

namespace OAI

noncomputable section

namespace InternalCatalan

namespace Case2Height
open Polynomial Set
open scoped BigOperators ComplexConjugate

theorem linear_den_norm_lower {x : ℝ} {z : ℂ} (hx : |x| ≤ 1) :
    1 - ‖z‖ ≤ ‖barrierTailLinearDen z x‖ := by
  have hm : ‖(x : ℂ) * z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg z)
  change 1 - ‖z‖ ≤ ‖(1 : ℂ) - (x : ℂ) * z‖
  exact (sub_le_sub_left hm 1).trans
    (by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) ((x : ℂ) * z))

theorem quadratic_den_norm_lower {x : ℝ} {z : ℂ} (hx : |x| ≤ 1)
    (hz : ‖z‖ ≤ 1) : (1 - ‖z‖) ^ 2 ≤ ‖barrierTailQuadraticDen z x‖ := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  have hA : 1 - ‖z‖ ≤ ‖(1 : ℂ) - z * realEnergyCirclePoint x‖ := by
    simpa only [norm_one, norm_mul, realEnergyCirclePoint_norm hx', mul_one] using
      norm_sub_norm_le (1 : ℂ) (z * realEnergyCirclePoint x)
  have hB : 1 - ‖z‖ ≤ ‖(1 : ℂ) - z * conj (realEnergyCirclePoint x)‖ := by
    simpa only [norm_one, norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hx', mul_one] using
      norm_sub_norm_le (1 : ℂ) (z * conj (realEnergyCirclePoint x))
  have hfactor :
      ((1 : ℂ) - z * realEnergyCirclePoint x) *
        (1 - z * conj (realEnergyCirclePoint x)) = barrierTailQuadraticDen z x := by
    calc
      _ = 1 - z * (realEnergyCirclePoint x + conj (realEnergyCirclePoint x)) +
          z ^ 2 * (realEnergyCirclePoint x * conj (realEnergyCirclePoint x)) := by ring
      _ = _ := by
        rw [realEnergyCirclePoint_add_conj, realEnergyCirclePoint_mul_conj hx']
        unfold barrierTailQuadraticDen
        ring
  calc
    _ ≤ ‖(1 : ℂ) - z * realEnergyCirclePoint x‖ *
        ‖(1 : ℂ) - z * conj (realEnergyCirclePoint x)‖ := by
      simpa only [pow_two] using mul_le_mul hA hB (sub_nonneg.mpr hz) (norm_nonneg _)
    _ = _ := by rw [← norm_mul, hfactor]

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

theorem actual_finite_bounds {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x| ≤ 55 ∧
    |(barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x| ≤ 55 ∧
    |(barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x| ≤ 10 := by
  refine ⟨(Case1Height.finiteU_abs_le_mass barrierP2Finite hx).trans ?_,
    (Case1Height.finiteU_abs_le_mass barrierV2Finite hx).trans ?_,
    (Case1Height.finitePower_abs_le_mass barrierV2Finite hx).trans ?_⟩
  all_goals norm_num [barrierP2Finite, barrierV2Finite, Finset.sum_range_succ]

theorem actual_tail_bounds {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierP2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re| ≤ 2800 ∧
    |(barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re| ≤ 832 ∧
    |(barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re| ≤ 52000 := by
  have hp : ∀ zr ∈ barrierP2Tail,
      ‖zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x‖ ≤ 280 := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierP2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (3 / 50 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd : (3 / 50 : ℝ) ^ 2 ≤ ‖barrierTailQuadraticDen zr.1 x‖ := by
      apply le_trans _ (quadratic_den_norm_lower hx hz1)
      nlinarith only [hgap, sq_nonneg (1 - ‖zr.1‖ - 3 / 50)]
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  have hvl : ∀ zr ∈ barrierV2Tail,
      ‖zr.2 * zr.1 / barrierTailLinearDen zr.1 x‖ ≤ 64 := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierV2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (2 / 125 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd := hgap.trans (linear_den_norm_lower hx (z := zr.1))
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  have hvq : ∀ zr ∈ barrierV2Tail,
      ‖zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x‖ ≤ 4000 := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierV2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (2 / 125 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd : (2 / 125 : ℝ) ^ 2 ≤ ‖barrierTailQuadraticDen zr.1 x‖ := by
      apply le_trans _ (quadratic_den_norm_lower hx hz1)
      nlinarith only [hgap, sq_nonneg (1 - ‖zr.1‖ - 2 / 125)]
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  constructor
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierP2Tail _ 280 hp).trans_eq (by rw [barrier_tail_lengths.1]; norm_num))
  constructor
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierV2Tail _ 64 hvl).trans_eq (by rw [barrier_tail_lengths.2]; norm_num))
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierV2Tail _ 4000 hvq).trans_eq (by rw [barrier_tail_lengths.2]; norm_num))

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

theorem X_formula_abs_le {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |barrierCase2XDerivativeFormula x| ≤ 120000 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  obtain ⟨hpu, _, hvp⟩ := actual_finite_bounds hx
  obtain ⟨hpt, hvt, _⟩ := actual_tail_bounds hx
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hd1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hA : |(19 / 48 : ℝ) / x| ≤ 566 := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ 120 := by
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
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)| ≤ 11420 := by
    rw [abs_mul]
    norm_num
    have hh := abs_add_le ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x)
      ((barrierP2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)
    linarith
  have hE : |(barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re| ≤ 842 := by
    have hh := abs_add_le ((barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x)
      ((barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re)
    linarith
  unfold barrierCase2XDerivativeFormula
  exact (abs_four_sub_le _ _ _ _ _).trans (by linarith)

theorem Y_formula_abs_le {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |barrierCase2YDerivativeFormula x| ≤ 120000 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  obtain ⟨_, hvu, _⟩ := actual_finite_bounds hx
  obtain ⟨_, _, hvt⟩ := actual_tail_bounds hx
  have hA : |(7 / 48 : ℝ) / x| ≤ 209 := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ 120 := by
    apply abs_div_le_const (abs_pos.mpr hgpos.ne')
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |2 * ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)| ≤ 104110 := by
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

end Case2Height

open Set

namespace Case2Height

theorem X_closed_bracket_margins (m : ℤ) (hm : m ∈ barrierCase2XBrackets)
    {x : ℝ} (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Ioo (-1 : ℝ) 1 ∧ |x| ≤ 1 ∧
      (7 / 10000 : ℝ) ≤ |x| ∧ (7 / 10000 : ℝ) ≤ 1 - x := by
  have he : (-1 : ℝ) < (barrierBracketLeft m : ℝ) ∧
      (barrierBracketRight m : ℝ) < 1 ∧
      ((barrierBracketRight m : ℝ) ≤ -(7 / 10000 : ℝ) ∨
        (7 / 10000 : ℝ) ≤ (barrierBracketLeft m : ℝ)) ∧
      (barrierBracketRight m : ℝ) ≤ 1 - (7 / 10000 : ℝ) := by
    simp only [barrierCase2XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> norm_num [barrierBracketLeft, barrierBracketRight]
  have hdomain : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨he.1.trans_le hx.1, hx.2.trans_lt he.2.1⟩
  refine ⟨hdomain, abs_le.mpr ⟨hdomain.1.le, hdomain.2.le⟩, ?_, ?_⟩
  · rcases he.2.2.1 with hnegative | hpositive
    · have ha := neg_le_abs x
      linarith [hx.2]
    · have ha := le_abs_self x
      linarith [hx.1]
  · linarith [hx.2, he.2.2.2]

theorem Y_closed_bracket_margins (m : ℤ) (hm : m ∈ barrierCase2YBrackets)
    {x : ℝ} (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Ioo (0 : ℝ) 1 ∧ |x| ≤ 1 ∧
      (7 / 10000 : ℝ) ≤ |x| ∧ (7 / 10000 : ℝ) ≤ 1 - x := by
  have he : (7 / 10000 : ℝ) ≤ (barrierBracketLeft m : ℝ) ∧
      (barrierBracketRight m : ℝ) ≤ 1 - (7 / 10000 : ℝ) := by
    simp only [barrierCase2YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> norm_num [barrierBracketLeft, barrierBracketRight]
  have hdomain : x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2, he.1, he.2]
  refine ⟨hdomain, ?_, ?_, ?_⟩
  · rw [abs_of_pos hdomain.1]
    exact hdomain.2.le
  · rw [abs_of_pos hdomain.1]
    exact he.1.trans hx.1
  · linarith [hx.2, he.2]

private theorem height_of_abs_variation {f : ℝ → ℝ} {m : ℤ} {x : ℝ}
    (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hvar : |f x - f (barrierBracketLeft m : ℝ)| ≤
      120000 * |x - (barrierBracketLeft m : ℝ)|) :
    f x ≤ f (barrierBracketLeft m : ℝ) + (24 / 1000000 : ℝ) := by
  have hdist : |x - (barrierBracketLeft m : ℝ)| ≤
      (barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    exact sub_le_sub_right hx.2 _
  have he : |f x - f (barrierBracketLeft m : ℝ)| ≤ (24 / 1000000 : ℝ) := by
    calc
      _ ≤ 120000 * |x - (barrierBracketLeft m : ℝ)| := hvar
      _ ≤ 120000 * ((barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdist (by norm_num)
      _ = (24 / 1000000 : ℝ) := by rw [Case1Height.actual_bracket_width]; norm_num
  have hs := (le_abs_self (f x - f (barrierBracketLeft m : ℝ))).trans he
  linarith

end Case2Height

theorem barrierCase2X_bracket_height (m : ℤ) (hm : m ∈ barrierCase2XBrackets)
    {x : ℝ} (hx : x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    barrierCase2X x ≤ barrierCase2X (barrierBracketLeft m : ℝ) +
      (24 / 1000000 : ℝ) := by
  have hxcc : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) :=
    ⟨hx.1.le, hx.2.le⟩
  apply Case2Height.height_of_abs_variation hxcc
  apply Case1Height.abs_sub_le_on_Icc
  · intro y hy
    obtain ⟨hyD, _, hy0, _⟩ := Case2Height.X_closed_bracket_margins m hm hy
    have h0 : y ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by norm_num) hy0)
    exact (barrierCase2X_hasDerivAt hyD h0).differentiableAt
  · intro y hy
    obtain ⟨hyD, hyabs, hy0, hy1⟩ := Case2Height.X_closed_bracket_margins m hm hy
    have h0 : y ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by norm_num) hy0)
    rw [(barrierCase2X_hasDerivAt hyD h0).deriv]
    exact Case2Height.X_formula_abs_le hyabs hy0 hy1
  · exact hxcc

theorem barrierCase2Y_bracket_height (m : ℤ) (hm : m ∈ barrierCase2YBrackets)
    {x : ℝ} (hx : x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    barrierCase2Y x ≤ barrierCase2Y (barrierBracketLeft m : ℝ) +
      (24 / 1000000 : ℝ) := by
  have hxcc : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) :=
    ⟨hx.1.le, hx.2.le⟩
  apply Case2Height.height_of_abs_variation hxcc
  apply Case1Height.abs_sub_le_on_Icc
  · intro y hy
    obtain ⟨hyD, _, _, _⟩ := Case2Height.Y_closed_bracket_margins m hm hy
    exact (barrierCase2Y_hasDerivAt hyD).differentiableAt
  · intro y hy
    obtain ⟨hyD, hyabs, hy0, hy1⟩ := Case2Height.Y_closed_bracket_margins m hm hy
    rw [(barrierCase2Y_hasDerivAt hyD).deriv]
    exact Case2Height.Y_formula_abs_le hyabs hy0 hy1
  · exact hxcc

end InternalCatalan

end

end OAI
