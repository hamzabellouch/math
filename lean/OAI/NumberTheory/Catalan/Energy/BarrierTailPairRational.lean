import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierComplex (a b : ℚ) : ℂ := ⟨(a : ℝ), (b : ℝ)⟩

def barrierConjugatePair (z r : ℂ) : List (ℂ × ℂ) :=
  [(z, r), (star z, star r)]

def barrierP2Finite : List ℤ :=
  [45559127, -50750856, -6578767, 13970217, 4786184, -4292433, -576704, 1311615, 671564, -346453]

def barrierV2Finite : List ℤ :=
  [-23910158, 21152432, -2885110, -11558199, 6485289, 1456821, -1912176, -2263524, 2742210, -1162454]

def barrierP1Finite : List ℤ :=
  [11913521, -79993701, -21956443, 37903579, 10744022, -2073193, 570246, -24939103]

def barrierV1Finite : List ℤ :=
  [-89913025, 52874280, 45168341, -30708629, -19269841, 33922112, 9819141, -16992389]

def barrierP2Tail : List (ℂ × ℂ) :=
  [((barrierComplex (85 / 100) 0), (barrierComplex (-9338452 / 100000000) 0))] ++
  [((barrierComplex (94 / 100) 0), (barrierComplex (-2141509 / 100000000) 0))] ++
  barrierConjugatePair (barrierComplex 0 (7 / 10)) (barrierComplex (-66277922 / 200000000) (31907569 / 200000000)) ++
  barrierConjugatePair (barrierComplex 0 (85 / 100)) (barrierComplex (-1231651 / 200000000) (-6002645 / 200000000)) ++
  barrierConjugatePair (barrierComplex (92 / 1000) (92 / 100)) (barrierComplex (-3225918 / 200000000) (-8928234 / 200000000)) ++
  barrierConjugatePair (barrierComplex (-92 / 1000) (92 / 100)) (barrierComplex (-2105536 / 200000000) (9091287 / 200000000))

def barrierV2Tail : List (ℂ × ℂ) :=
  [((barrierComplex (-8 / 10) 0), (barrierComplex (15199211 / 100000000) 0))] ++
  [((barrierComplex (-96 / 100) 0), (barrierComplex (4451662 / 100000000) 0))] ++
  [((barrierComplex (88 / 100) 0), (barrierComplex (2545398 / 100000000) 0))] ++
  [((barrierComplex (95 / 100) 0), (barrierComplex (-4932634 / 100000000) 0))] ++
  [((barrierComplex (984 / 1000) 0), (barrierComplex (11618157 / 100000000) 0))] ++
  barrierConjugatePair (barrierComplex 0 (78 / 100)) (barrierComplex (27238714 / 200000000) (38447936 / 200000000)) ++
  barrierConjugatePair (barrierComplex 0 (9 / 10)) (barrierComplex (-31341084 / 200000000) (30188786 / 200000000)) ++
  barrierConjugatePair (barrierComplex 0 (955 / 1000)) (barrierComplex (-6693542 / 200000000) (-11912254 / 200000000)) ++
  barrierConjugatePair (barrierComplex 0 (984 / 1000)) (barrierComplex (2055213 / 200000000) (21715849 / 200000000))

def barrierLambda2 : ℝ := 0
def barrierLambda1 : ℝ := 247405979 / 100000000

def barrierFiniteCoeff (cs : List ℤ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (cs.getD (k - 1) 0 : ℝ) / 100000000

def barrierTrial (cs : List ℤ) (tail : List (ℂ × ℂ)) (k : ℕ) : ℝ :=
  if k = 0 then 0 else barrierFiniteCoeff cs k +
    (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re

def barrierP2 : ℕ → ℝ := barrierTrial barrierP2Finite barrierP2Tail
def barrierV2 : ℕ → ℝ := barrierTrial barrierV2Finite barrierV2Tail
def barrierP1 : ℕ → ℝ := barrierTrial barrierP1Finite []
def barrierV1 : ℕ → ℝ := barrierTrial barrierV1Finite []

theorem barrier_finite_lengths :
    barrierP2Finite.length = 10 ∧ barrierV2Finite.length = 10 ∧
    barrierP1Finite.length = 8 ∧ barrierV1Finite.length = 8 := by decide

theorem barrier_tail_lengths : barrierP2Tail.length = 10 ∧ barrierV2Tail.length = 13 := by
  norm_num [barrierP2Tail, barrierV2Tail, barrierConjugatePair]

theorem barrier_lambdas : barrierLambda2 = 0 ∧ 0 ≤ barrierLambda1 ∧
    barrierLambda1 < 5 / 2 := by
  norm_num [barrierLambda1, barrierLambda2]

theorem barrierP2_finite_abs_lt_one :
    ∀ a ∈ barrierP2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP2Finite]

theorem barrierV2_finite_abs_lt_one :
    ∀ a ∈ barrierV2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV2Finite]

theorem barrierP1_finite_abs_lt_one :
    ∀ a ∈ barrierP1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP1Finite]

theorem barrierV1_finite_abs_lt_one :
    ∀ a ∈ barrierV1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV1Finite]

theorem barrierP2_tail_norm_bounds :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (94 / 100 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierP2Tail,
      Complex.normSq zr.1 ≤ (94 / 100 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierV2_tail_norm_bounds :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (984 / 1000 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierV2Tail,
      Complex.normSq zr.1 ≤ (984 / 1000 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierFiniteCoeff_abs_le (cs : List ℤ) (hlen : cs.length ≤ 10)
    (hcoeff : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1) (k : ℕ) :
    |barrierFiniteCoeff cs k| ≤ 2 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · subst k
    norm_num [barrierFiniteCoeff]
  rw [barrierFiniteCoeff, ite_eq_right hk]
  by_cases hi : k - 1 < cs.length
  · have hmem : cs.getD (k - 1) 0 ∈ cs := by
      rw [List.getD_eq_getElem cs 0 hi]
      exact List.getElem_mem hi
    have hk10 : k ≤ 10 := by omega
    have hpow : (99 / 100 : ℝ) ^ 10 ≤ (99 / 100 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk10
    calc
      |(cs.getD (k - 1) 0 : ℝ) / 100000000| ≤ 1 :=
        le_of_lt (hcoeff _ hmem)
      _ ≤ 2 * (99 / 100 : ℝ) ^ 10 := by norm_num
      _ ≤ 2 * (99 / 100 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
  · rw [List.getD_eq_default cs 0 (Nat.le_of_not_gt hi)]
    simp only [Int.cast_zero, zero_div, abs_zero]
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)

def barrierTailLinearDen (z : ℂ) (x : ℝ) : ℂ := 1 - (x : ℂ) * z

def barrierTailQuadraticDen (z : ℂ) (x : ℝ) : ℂ :=
  1 - 2 * (x : ℂ) * z + z ^ 2

theorem barrierTailLinearDen_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ < 1) : barrierTailLinearDen z x ≠ 0 := by
  have hnorm : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |x| * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ < 1 := by simpa only [one_mul] using hz
  intro hzero
  have hmul : (x : ℂ) * z = 1 := (sub_eq_zero.mp hzero).symm
  rw [hmul, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

theorem barrierTailQuadraticDen_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ < 1) : barrierTailQuadraticDen z x ≠ 0 := by
  have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
  have hn : Complex.normSq z < 1 :=
    lt_of_not_ge (fun h => (not_le_of_gt hz) (Complex.one_le_normSq_iff.mp h))
  have hnorm : z.re ^ 2 + z.im ^ 2 < 1 := by
    simpa only [Complex.normSq_apply, pow_two] using hn
  intro hzero
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  norm_num [barrierTailQuadraticDen, pow_two] at hre him
  have hprod : z.im * (z.re - x) = 0 := by nlinarith [him]
  have hax : z.re = x := by
    rcases mul_eq_zero.mp hprod with hb | ha
    · have hre0 := hre
      rw [hb] at hre0
      have hs : (z.re - x) ^ 2 = 0 := by
        nlinarith [sq_nonneg (z.re - x)]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · exact sub_eq_zero.mp ha
  rw [hax] at hre hnorm
  nlinarith

theorem barrierTailLinearDen_prod_ne_zero (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    (tail.map (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro hzero
  obtain ⟨zr, hzr, hz⟩ := List.mem_map.mp hzero
  exact barrierTailLinearDen_ne_zero hx (htail zr hzr) hz

theorem barrierTailQuadraticDen_prod_ne_zero (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    (tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro hzero
  obtain ⟨zr, hzr, hz⟩ := List.mem_map.mp hzero
  exact barrierTailQuadraticDen_ne_zero hx (htail zr hzr) hz

def barrierCase2QXValue (x : ℝ) : ℂ :=
  (x : ℂ) * (1 - (x : ℂ)) * (1 + (x : ℂ) ^ 2) *
    (barrierP2Tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod *
    (barrierV2Tail.map (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod

def barrierCase2QYValue (x : ℝ) : ℂ :=
  (x : ℂ) * (1 - (x : ℂ)) *
    (barrierV2Tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod

private theorem barrierP2_tail_base_lt_one :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierP2_tail_norm_bounds zr hzr).1 (by norm_num)

private theorem barrierV2_tail_base_lt_one :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)

theorem barrierCase2QXValue_ne_zero {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) : barrierCase2QXValue x ≠ 0 := by
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hx1' : 1 - (x : ℂ) ≠ 0 := by
    have h : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
    exact_mod_cast h
  have hsq : 1 + (x : ℂ) ^ 2 ≠ 0 := by
    have h : (1 + x ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    exact_mod_cast h
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hx0' hx1') hsq)
      (barrierTailQuadraticDen_prod_ne_zero barrierP2Tail barrierP2_tail_base_lt_one hx))
    (barrierTailLinearDen_prod_ne_zero barrierV2Tail barrierV2_tail_base_lt_one hx)

theorem barrierCase2QYValue_ne_zero {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) : barrierCase2QYValue x ≠ 0 := by
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hx1' : 1 - (x : ℂ) ≠ 0 := by
    have h : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
    exact_mod_cast h
  exact mul_ne_zero (mul_ne_zero hx0' hx1')
    (barrierTailQuadraticDen_prod_ne_zero barrierV2Tail barrierV2_tail_base_lt_one hx)

theorem barrierComplex_real_pow (a : ℚ) (k : ℕ) :
    (barrierComplex a 0) ^ k = (((a : ℝ) ^ k : ℝ) : ℂ) := by
  have h : barrierComplex a 0 = ((a : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [barrierComplex]
  rw [h, Complex.ofReal_pow]

theorem barrierComplex_imaginary_pow (b : ℚ) (k : ℕ) :
    (barrierComplex 0 b) ^ k = (((b : ℝ) ^ k : ℝ) : ℂ) * Complex.I ^ k := by
  have h : barrierComplex 0 b = ((b : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [barrierComplex]
  rw [h, mul_pow, Complex.ofReal_pow]

theorem barrierConjugatePair_power_re (z r : ℂ) (k : ℕ) :
    ((barrierConjugatePair z r).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re =
      2 * (r * z ^ k).re := by
  have h : star r * star z ^ k = star (r * z ^ k) := by simp
  simp only [barrierConjugatePair, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [h]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

def barrierAxisPhase (c d : ℝ) (k : ℕ) : ℝ :=
  c * (Complex.I ^ k).re - d * (Complex.I ^ k).im

theorem barrierConjugatePair_imaginary_power_re (b c d : ℚ) (k : ℕ) :
    ((barrierConjugatePair (barrierComplex 0 b) (barrierComplex c d)).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re =
      2 * barrierAxisPhase (c : ℝ) (d : ℝ) k * (b : ℝ) ^ k := by
  rw [barrierConjugatePair_power_re, barrierComplex_imaginary_pow]
  simp only [barrierAxisPhase, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    barrierComplex]
  ring

def barrierV2CoefficientFormula (k : ℕ) : ℝ :=
  barrierFiniteCoeff barrierV2Finite k +
  (15199211 / 100000000) * (-8 / 10) ^ k +
  (4451662 / 100000000) * (-96 / 100) ^ k +
  (2545398 / 100000000) * (88 / 100) ^ k +
  (-4932634 / 100000000) * (95 / 100) ^ k +
  (11618157 / 100000000) * (984 / 1000) ^ k +
  2 * barrierAxisPhase (27238714 / 200000000) (38447936 / 200000000) k * (78 / 100) ^ k +
  2 * barrierAxisPhase (-31341084 / 200000000) (30188786 / 200000000) k * (9 / 10) ^ k +
  2 * barrierAxisPhase (-6693542 / 200000000) (-11912254 / 200000000) k * (955 / 1000) ^ k +
  2 * barrierAxisPhase (2055213 / 200000000) (21715849 / 200000000) k * (984 / 1000) ^ k

theorem barrierV2_eq_coefficientFormula (k : ℕ) (hk : k ≠ 0) :
    barrierV2 k = barrierV2CoefficientFormula k := by
  simp only [barrierV2, barrierTrial, ite_eq_right hk, barrierV2Tail,
    List.map_append, List.sum_append, Complex.add_re]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [barrierConjugatePair_imaginary_power_re, barrierComplex_real_pow]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, barrierComplex]
  norm_num [barrierV2CoefficientFormula]
  ring

def barrierP2NormRows : List (ℝ × ℝ) :=
  [(85/100, 9338452/100000000), (94/100, 2141509/100000000),
   (7/10, 98185491/200000000), (7/10, 98185491/200000000),
   (85/100, 7234296/200000000), (85/100, 7234296/200000000),
   (93/100, 12154152/200000000), (93/100, 12154152/200000000),
   (93/100, 11196823/200000000), (93/100, 11196823/200000000)]

def barrierV2NormRows : List (ℝ × ℝ) :=
  [(8/10, 15199211/100000000), (96/100, 4451662/100000000),
   (88/100, 2545398/100000000), (95/100, 4932634/100000000),
   (984/1000, 11618157/100000000),
   (78/100, 65686650/200000000), (78/100, 65686650/200000000),
   (9/10, 61529870/200000000), (9/10, 61529870/200000000),
   (955/1000, 18605796/200000000), (955/1000, 18605796/200000000),
   (984/1000, 23771062/200000000), (984/1000, 23771062/200000000)]

def barrierNormMajorant (rows : List (ℝ × ℝ)) (k : ℕ) : ℝ :=
  (rows.map (fun br => br.2 * br.1 ^ k)).sum

private theorem norm_le_of_normSq_le {z : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (hz : Complex.normSq z ≤ a ^ 2) : ‖z‖ ≤ a := by
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

private theorem normRows_of_sq {tail : List (ℂ × ℂ)} {rows : List (ℝ × ℝ)}
    (h : List.Forall₂ (fun zr br => 0 ≤ br.1 ∧ 0 ≤ br.2 ∧
      Complex.normSq zr.1 ≤ br.1 ^ 2 ∧ Complex.normSq zr.2 ≤ br.2 ^ 2) tail rows) :
    List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2) tail rows := by
  exact h.imp (fun zr br hb =>
    ⟨norm_le_of_normSq_le hb.1 hb.2.2.1,
      norm_le_of_normSq_le hb.2.1 hb.2.2.2⟩)

theorem barrierP2_normRows :
    List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2)
      barrierP2Tail barrierP2NormRows := by
  apply normRows_of_sq
  norm_num [barrierP2Tail, barrierP2NormRows, barrierConjugatePair,
    barrierComplex, Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]

theorem barrierV2_normRows :
    List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2)
      barrierV2Tail barrierV2NormRows := by
  apply normRows_of_sq
  norm_num [barrierV2Tail, barrierV2NormRows, barrierConjugatePair,
    barrierComplex, Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]

theorem barrier_tail_norm_majorant {tail : List (ℂ × ℂ)} {rows : List (ℝ × ℝ)}
    (h : List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2) tail rows)
    (k : ℕ) :
    ‖(tail.map (fun zr => zr.2 * zr.1 ^ k)).sum‖ ≤ barrierNormMajorant rows k := by
  induction h with
  | nil => simp [barrierNormMajorant]
  | @cons zr br tail rows hb hrest ih =>
    have hbr0 : 0 ≤ br.1 := (norm_nonneg zr.1).trans hb.1
    have hbw0 : 0 ≤ br.2 := (norm_nonneg zr.2).trans hb.2
    have hterm : ‖zr.2 * zr.1 ^ k‖ ≤ br.2 * br.1 ^ k := by
      rw [norm_mul, norm_pow]
      gcongr
      · exact hb.2
      · exact hb.1
    simpa only [List.map_cons, List.sum_cons, barrierNormMajorant] using
      (norm_add_le (zr.2 * zr.1 ^ k)
        ((tail.map (fun zr => zr.2 * zr.1 ^ k)).sum)).trans (add_le_add hterm ih)

theorem barrier_normMajorant_shift (rows : List (ℝ × ℝ)) (r : ℝ)
    (hb : ∀ br ∈ rows, 0 ≤ br.1 ∧ br.1 ≤ r ∧ 0 ≤ br.2) (K j : ℕ) :
    barrierNormMajorant rows (K + j) ≤ barrierNormMajorant rows K * r ^ j := by
  induction rows with
  | nil => simp [barrierNormMajorant]
  | cons br rows ih =>
    have hbr := hb br List.mem_cons_self
    have hbr0 : 0 ≤ br.1 := hbr.1
    have hbw0 : 0 ≤ br.2 := hbr.2.2
    have hi := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hp : br.2 * br.1 ^ (K + j) ≤ (br.2 * br.1 ^ K) * r ^ j := by
      rw [pow_add]
      calc
        _ = (br.2 * br.1 ^ K) * br.1 ^ j := by ring
        _ ≤ _ := by gcongr; exact hbr.2.1
    simpa only [barrierNormMajorant, List.map_cons, List.sum_cons, add_mul] using
      add_le_add hp hi

theorem barrierTrial_abs_le_majorant (cs : List ℤ) (tail : List (ℂ × ℂ))
    (rows : List (ℝ × ℝ))
    (hb : List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2) tail rows)
    (k : ℕ) (hk : cs.length < k) :
    |barrierTrial cs tail k| ≤ barrierNormMajorant rows k := by
  have hk0 : k ≠ 0 := by omega
  have hlen : cs.length ≤ k - 1 := by omega
  simp only [barrierTrial, ite_eq_right hk0, barrierFiniteCoeff,
    List.getD_eq_default cs 0 hlen, Int.cast_zero, zero_div, zero_add]
  exact (Complex.abs_re_le_norm _).trans (barrier_tail_norm_majorant hb k)

theorem barrierP2_tail_decay (j : ℕ) :
    |barrierP2 (j + 60 + 1)| ≤ (33 / 10000 : ℝ) * (94 / 100 : ℝ) ^ j := by
  have hstart : barrierNormMajorant barrierP2NormRows 61 ≤ (33 / 10000 : ℝ) := by
    norm_num [barrierNormMajorant, barrierP2NormRows]
  have hr : ∀ br ∈ barrierP2NormRows, 0 ≤ br.1 ∧ br.1 ≤ (94 / 100 : ℝ) ∧ 0 ≤ br.2 := by
    norm_num [barrierP2NormRows]
  calc
    _ ≤ barrierNormMajorant barrierP2NormRows (j + 60 + 1) :=
      barrierTrial_abs_le_majorant _ _ _ barrierP2_normRows _ (by
        rw [barrier_finite_lengths.1]; omega)
    _ = barrierNormMajorant barrierP2NormRows (61 + j) := by congr 1; omega
    _ ≤ barrierNormMajorant barrierP2NormRows 61 * (94 / 100 : ℝ) ^ j :=
      barrier_normMajorant_shift _ _ hr 61 j
    _ ≤ _ := mul_le_mul_of_nonneg_right hstart (by positivity)

theorem barrierV2_tail_decay (j : ℕ) :
    |barrierV2 (j + 225 + 1)| ≤ (93 / 10000 : ℝ) * (984 / 1000 : ℝ) ^ j := by
  have hstart : barrierNormMajorant barrierV2NormRows 226 ≤ (93 / 10000 : ℝ) := by
    norm_num [barrierNormMajorant, barrierV2NormRows]
  have hr : ∀ br ∈ barrierV2NormRows, 0 ≤ br.1 ∧ br.1 ≤ (984 / 1000 : ℝ) ∧ 0 ≤ br.2 := by
    norm_num [barrierV2NormRows]
  calc
    _ ≤ barrierNormMajorant barrierV2NormRows (j + 225 + 1) :=
      barrierTrial_abs_le_majorant _ _ _ barrierV2_normRows _ (by
        rw [barrier_finite_lengths.2.1]; omega)
    _ = barrierNormMajorant barrierV2NormRows (226 + j) := by congr 1; omega
    _ ≤ barrierNormMajorant barrierV2NormRows 226 * (984 / 1000 : ℝ) ^ j :=
      barrier_normMajorant_shift _ _ hr 226 j
    _ ≤ _ := mul_le_mul_of_nonneg_right hstart (by positivity)

open Polynomial

private theorem barrier_conjugate_quotient_re (n d : ℂ) :
    (n / d + star n / star d).re =
      2 * (n.re * d.re + n.im * d.im) / (d.re ^ 2 + d.im ^ 2) := by
  have hc : star n / star d = star (n / d) := by
    simp only [Complex.star_def, map_div₀]
  rw [hc]
  simp only [Complex.star_def, Complex.add_re, Complex.conj_re, Complex.div_re,
    Complex.normSq_apply, pow_two]
  ring

private theorem barrierTailLinearDen_star (z : ℂ) (x : ℝ) :
    barrierTailLinearDen (star z) x = star (barrierTailLinearDen z x) := by
  simp [barrierTailLinearDen]

private theorem barrierTailQuadraticDen_star (z : ℂ) (x : ℝ) :
    barrierTailQuadraticDen (star z) x = star (barrierTailQuadraticDen z x) := by
  simp [barrierTailQuadraticDen]

theorem barrierConjugatePair_linear_re (z r : ℂ) (x : ℝ) :
    ((barrierConjugatePair z r).map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re =
      2 * ((r * z).re * (1 - x * z.re) - (r * z).im * x * z.im) /
        ((1 - x * z.re) ^ 2 + (x * z.im) ^ 2) := by
  simp only [barrierConjugatePair, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hn : star r * star z = star (r * z) := by simp
  rw [barrierTailLinearDen_star, hn, barrier_conjugate_quotient_re]
  simp only [barrierTailLinearDen, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_im, Complex.one_im, Complex.mul_im]
  congr 1 <;> ring

theorem barrierConjugatePair_quadratic_re (z r : ℂ) (x : ℝ) :
    ((barrierConjugatePair z r).map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      2 * ((r * z).re * (1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2) +
        (r * z).im * (2 * z.im * (z.re - x))) /
        ((1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2) ^ 2 +
          (2 * z.im * (z.re - x)) ^ 2) := by
  simp only [barrierConjugatePair, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hn : star r * star z = star (r * z) := by simp
  rw [barrierTailQuadraticDen_star, hn, barrier_conjugate_quotient_re]
  have hre : (barrierTailQuadraticDen z x).re =
      1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2 := by
    simp [barrierTailQuadraticDen, pow_two]
    ring
  have him : (barrierTailQuadraticDen z x).im = 2 * z.im * (z.re - x) := by
    simp [barrierTailQuadraticDen, pow_two]
    ring
  rw [hre, him]

def barrierPairLinearQ (a b : ℚ) : ℚ[X] :=
  (1 - C a * X) ^ 2 + (C b * X) ^ 2

def barrierPairLinearA (a b c d : ℚ) : ℚ[X] :=
  2 * (C (c * a - d * b) * (1 - C a * X) - C (c * b + d * a) * C b * X)

def barrierPairQuadraticQ (a b : ℚ) : ℚ[X] :=
  (1 - 2 * C a * X + C (a ^ 2 - b ^ 2)) ^ 2 +
    (2 * C b * (C a - X)) ^ 2

def barrierPairQuadraticA (a b c d : ℚ) : ℚ[X] :=
  2 * (C (c * a - d * b) * (1 - 2 * C a * X + C (a ^ 2 - b ^ 2)) +
    C (c * b + d * a) * (2 * C b * (C a - X)))

theorem barrierConjugatePair_linear_eq_ratPolynomial
    (a b c d : ℚ) (x : ℝ) :
    ((barrierConjugatePair (barrierComplex a b) (barrierComplex c d)).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re =
      (barrierPairLinearA a b c d).eval₂ (Rat.castHom ℝ) x /
        (barrierPairLinearQ a b).eval₂ (Rat.castHom ℝ) x := by
  rw [barrierConjugatePair_linear_re]
  simp only [barrierPairLinearA, barrierPairLinearQ, eval₂_mul, eval₂_add,
    eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, eval₂_one, eval₂_ofNat,
    map_mul, map_sub, map_add, Rat.coe_castHom, barrierComplex, Complex.mul_re, Complex.mul_im]
  congr 1 <;> ring

theorem barrierConjugatePair_quadratic_eq_ratPolynomial
    (a b c d : ℚ) (x : ℝ) :
    ((barrierConjugatePair (barrierComplex a b) (barrierComplex c d)).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      (barrierPairQuadraticA a b c d).eval₂ (Rat.castHom ℝ) x /
        (barrierPairQuadraticQ a b).eval₂ (Rat.castHom ℝ) x := by
  rw [barrierConjugatePair_quadratic_re]
  simp only [barrierPairQuadraticA, barrierPairQuadraticQ, eval₂_mul, eval₂_add,
    eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, eval₂_one, eval₂_ofNat,
    map_mul, map_sub, map_add, map_pow, Rat.coe_castHom, barrierComplex, Complex.mul_re, Complex.mul_im]
  congr 1 <;> ring

private theorem barrierPairLinearQ_eval_eq_normSq (a b : ℚ) (x : ℝ) :
    (barrierPairLinearQ a b).eval₂ (Rat.castHom ℝ) x =
      Complex.normSq (barrierTailLinearDen (barrierComplex a b) x) := by
  simp [barrierPairLinearQ, eval₂_pow, barrierTailLinearDen,
    barrierComplex, Complex.normSq_apply]
  ring

private theorem barrierPairQuadraticQ_eval_eq_normSq (a b : ℚ) (x : ℝ) :
    (barrierPairQuadraticQ a b).eval₂ (Rat.castHom ℝ) x =
      Complex.normSq (barrierTailQuadraticDen (barrierComplex a b) x) := by
  simp [barrierPairQuadraticQ, barrierTailQuadraticDen,
    barrierComplex, Complex.normSq_apply, pow_two]
  ring

theorem barrierPairLinearQ_eval_pos (a b : ℚ) {x : ℝ}
    (hx : |x| ≤ 1) (hz : ‖barrierComplex a b‖ < 1) :
    0 < (barrierPairLinearQ a b).eval₂ (Rat.castHom ℝ) x := by
  rw [barrierPairLinearQ_eval_eq_normSq]
  exact Complex.normSq_pos.mpr (barrierTailLinearDen_ne_zero hx hz)

theorem barrierPairQuadraticQ_eval_pos (a b : ℚ) {x : ℝ}
    (hx : |x| ≤ 1) (hz : ‖barrierComplex a b‖ < 1) :
    0 < (barrierPairQuadraticQ a b).eval₂ (Rat.castHom ℝ) x := by
  rw [barrierPairQuadraticQ_eval_eq_normSq]
  exact Complex.normSq_pos.mpr (barrierTailQuadraticDen_ne_zero hx hz)

end InternalCatalan

end

end OAI
