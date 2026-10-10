import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.GetD
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import OAI.NumberTheory.Catalan.Energy.BarrierRationalSumNumerator
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneDescartesX0

namespace OAI

noncomputable section

namespace InternalCatalan

structure BarrierRationalPairRow where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

def barrierP2RealRows : List (ℚ × ℚ) :=
  [(85 / 100, -9338452 / 100000000), (94 / 100, -2141509 / 100000000)]

def barrierP2PairRows : List BarrierRationalPairRow :=
  [⟨0, 7 / 10, -66277922 / 200000000, 31907569 / 200000000⟩,
   ⟨0, 85 / 100, -1231651 / 200000000, -6002645 / 200000000⟩,
   ⟨92 / 1000, 92 / 100, -3225918 / 200000000, -8928234 / 200000000⟩,
   ⟨-92 / 1000, 92 / 100, -2105536 / 200000000, 9091287 / 200000000⟩]

def barrierV2RealRows : List (ℚ × ℚ) :=
  [(-8 / 10, 15199211 / 100000000), (-96 / 100, 4451662 / 100000000),
   (88 / 100, 2545398 / 100000000), (95 / 100, -4932634 / 100000000),
   (984 / 1000, 11618157 / 100000000)]

def barrierV2PairRows : List BarrierRationalPairRow :=
  [⟨0, 78 / 100, 27238714 / 200000000, 38447936 / 200000000⟩,
   ⟨0, 9 / 10, -31341084 / 200000000, 30188786 / 200000000⟩,
   ⟨0, 955 / 1000, -6693542 / 200000000, -11912254 / 200000000⟩,
   ⟨0, 984 / 1000, 2055213 / 200000000, 21715849 / 200000000⟩]

def barrierExpandRealRows (rs : List (ℚ × ℚ)) : List (ℂ × ℂ) :=
  rs.map (fun ac : ℚ × ℚ => (barrierComplex ac.1 0, barrierComplex ac.2 0))

def barrierExpandPairRow (row : BarrierRationalPairRow) : List (ℂ × ℂ) :=
  barrierConjugatePair (barrierComplex row.a row.b) (barrierComplex row.c row.d)

def barrierExpandPairRows (rs : List BarrierRationalPairRow) : List (ℂ × ℂ) :=
  rs.flatMap barrierExpandPairRow

theorem barrierP2Tail_eq_grouped :
    barrierP2Tail = barrierExpandRealRows barrierP2RealRows ++
      barrierExpandPairRows barrierP2PairRows := by rfl

theorem barrierV2Tail_eq_grouped :
    barrierV2Tail = barrierExpandRealRows barrierV2RealRows ++
      barrierExpandPairRows barrierV2PairRows := by rfl

open Polynomial

def barrierRealLinearQ (a : ℚ) : ℚ[X] := 1 - C a * X

def barrierRealQuadraticQ (a : ℚ) : ℚ[X] := 1 - 2 * C a * X + C (a ^ 2)

def barrierGroupedLinearQ (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : ℚ[X] :=
  (rs.map (fun ac : ℚ × ℚ => barrierRealLinearQ ac.1)).prod *
    (ps.map (fun row : BarrierRationalPairRow => barrierPairLinearQ row.a row.b)).prod

def barrierGroupedQuadraticQ (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : ℚ[X] :=
  (rs.map (fun ac : ℚ × ℚ => barrierRealQuadraticQ ac.1)).prod *
    (ps.map (fun row : BarrierRationalPairRow => barrierPairQuadraticQ row.a row.b)).prod

private theorem barrierRealLinearQ_eval_complex (a : ℚ) (x : ℝ) :
    (barrierRealLinearQ a).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      barrierTailLinearDen (barrierComplex a 0) x := by
  apply Complex.ext <;> simp [barrierRealLinearQ, barrierTailLinearDen, barrierComplex]
  ring

private theorem barrierRealQuadraticQ_eval_complex (a : ℚ) (x : ℝ) :
    (barrierRealQuadraticQ a).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      barrierTailQuadraticDen (barrierComplex a 0) x := by
  apply Complex.ext <;>
    simp [barrierRealQuadraticQ, barrierTailQuadraticDen, barrierComplex, pow_two]
  ring

private theorem barrierPairLinearQ_eval_complex (row : BarrierRationalPairRow) (x : ℝ) :
    (barrierPairLinearQ row.a row.b).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandPairRow row).map
        (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod := by
  apply Complex.ext <;>
    simp [barrierPairLinearQ, barrierExpandPairRow, barrierConjugatePair,
      barrierTailLinearDen, barrierComplex, pow_two]
  <;> ring

private theorem barrierPairQuadraticQ_eval_complex (row : BarrierRationalPairRow) (x : ℝ) :
    (barrierPairQuadraticQ row.a row.b).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandPairRow row).map
        (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  apply Complex.ext <;>
    simp [barrierPairQuadraticQ, barrierExpandPairRow, barrierConjugatePair,
      barrierTailQuadraticDen, barrierComplex, pow_two]
  <;> ring

private theorem barrier_prod_map_flatMap {α β : Type*} (rs : List α)
    (g : α → List β) (f : β → ℂ) :
    ((rs.flatMap g).map f).prod = (rs.map (fun r => ((g r).map f).prod)).prod := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]

private theorem barrierGroupedLinearQ_eval_complex (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    (barrierGroupedLinearQ rs ps).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandRealRows rs ++ barrierExpandPairRows ps).map
        (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod := by
  simp only [barrierGroupedLinearQ, eval₂_mul, eval₂_list_prod,
    barrierExpandRealRows, barrierExpandPairRows, List.map_append, List.prod_append,
    barrier_prod_map_flatMap, List.map_map, Function.comp_def,
    barrierRealLinearQ_eval_complex, barrierPairLinearQ_eval_complex]

private theorem barrierGroupedQuadraticQ_eval_complex (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    (barrierGroupedQuadraticQ rs ps).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandRealRows rs ++ barrierExpandPairRows ps).map
        (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  simp only [barrierGroupedQuadraticQ, eval₂_mul, eval₂_list_prod,
    barrierExpandRealRows, barrierExpandPairRows, List.map_append, List.prod_append,
    barrier_prod_map_flatMap, List.map_map, Function.comp_def,
    barrierRealQuadraticQ_eval_complex, barrierPairQuadraticQ_eval_complex]

def barrierP2QuadraticQ : ℚ[X] :=
  barrierGroupedQuadraticQ barrierP2RealRows barrierP2PairRows

def barrierV2LinearQ : ℚ[X] :=
  barrierGroupedLinearQ barrierV2RealRows barrierV2PairRows

def barrierV2QuadraticQ : ℚ[X] :=
  barrierGroupedQuadraticQ barrierV2RealRows barrierV2PairRows

theorem barrierP2QuadraticQ_eval_complex (x : ℝ) :
    barrierP2QuadraticQ.eval₂ (Rat.castHom ℂ) (x : ℂ) =
      (barrierP2Tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  rw [barrierP2Tail_eq_grouped]
  exact barrierGroupedQuadraticQ_eval_complex _ _ x

theorem barrierV2LinearQ_eval_complex (x : ℝ) :
    barrierV2LinearQ.eval₂ (Rat.castHom ℂ) (x : ℂ) =
      (barrierV2Tail.map (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod := by
  rw [barrierV2Tail_eq_grouped]
  exact barrierGroupedLinearQ_eval_complex _ _ x

theorem barrierV2QuadraticQ_eval_complex (x : ℝ) :
    barrierV2QuadraticQ.eval₂ (Rat.castHom ℂ) (x : ℂ) =
      (barrierV2Tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  rw [barrierV2Tail_eq_grouped]
  exact barrierGroupedQuadraticQ_eval_complex _ _ x

def barrierCase2QX : ℚ[X] :=
  X * (1 - X) * (1 + X ^ 2) * barrierP2QuadraticQ * barrierV2LinearQ

def barrierCase2QY : ℚ[X] := X * (1 - X) * barrierV2QuadraticQ

theorem barrierCase2QX_eval_complex (x : ℝ) :
    barrierCase2QX.eval₂ (Rat.castHom ℂ) (x : ℂ) = barrierCase2QXValue x := by
  simp only [barrierCase2QX, eval₂_mul, eval₂_sub, eval₂_add, eval₂_pow,
    eval₂_X, eval₂_one, barrierP2QuadraticQ_eval_complex,
    barrierV2LinearQ_eval_complex, barrierCase2QXValue]

theorem barrierCase2QY_eval_complex (x : ℝ) :
    barrierCase2QY.eval₂ (Rat.castHom ℂ) (x : ℂ) = barrierCase2QYValue x := by
  simp only [barrierCase2QY, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one,
    barrierV2QuadraticQ_eval_complex, barrierCase2QYValue]

private theorem barrier_ratPolynomial_eval_complex (p : ℚ[X]) (x : ℝ) :
    ((p.eval₂ (Rat.castHom ℝ) x : ℝ) : ℂ) = p.eval₂ (Rat.castHom ℂ) (x : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

theorem barrierCase2QX_eval_ne_zero {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    barrierCase2QX.eval₂ (Rat.castHom ℝ) x ≠ 0 := by
  intro hzero
  apply barrierCase2QXValue_ne_zero hx hx0 hx1
  rw [← barrierCase2QX_eval_complex, ← barrier_ratPolynomial_eval_complex]
  simp only [hzero, Complex.ofReal_zero]

theorem barrierCase2QY_eval_ne_zero {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    barrierCase2QY.eval₂ (Rat.castHom ℝ) x ≠ 0 := by
  intro hzero
  apply barrierCase2QYValue_ne_zero hx hx0 hx1
  rw [← barrierCase2QY_eval_complex, ← barrier_ratPolynomial_eval_complex]
  simp only [hzero, Complex.ofReal_zero]

open Polynomial

def barrierGroupedLinearTailValue (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) : ℝ :=
  (rs.map (fun ac : ℚ × ℚ =>
    (ac.2 : ℝ) * (ac.1 : ℝ) / (1 - (ac.1 : ℝ) * x))).sum +
  (ps.map (fun row : BarrierRationalPairRow =>
    (barrierPairLinearA row.a row.b row.c row.d).eval₂ (Rat.castHom ℝ) x /
      (barrierPairLinearQ row.a row.b).eval₂ (Rat.castHom ℝ) x)).sum

def barrierGroupedQuadraticTailValue (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) : ℝ :=
  (rs.map (fun ac : ℚ × ℚ =>
    (ac.2 : ℝ) * (ac.1 : ℝ) /
      (1 - 2 * (ac.1 : ℝ) * x + (ac.1 : ℝ) ^ 2))).sum +
  (ps.map (fun row : BarrierRationalPairRow =>
    (barrierPairQuadraticA row.a row.b row.c row.d).eval₂ (Rat.castHom ℝ) x /
      (barrierPairQuadraticQ row.a row.b).eval₂ (Rat.castHom ℝ) x)).sum

private theorem barrierComplex_real (a : ℚ) :
    barrierComplex a 0 = ((a : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [barrierComplex]

private theorem barrier_realTailLinear_re (a c : ℚ) (x : ℝ) :
    (barrierComplex c 0 * barrierComplex a 0 /
      barrierTailLinearDen (barrierComplex a 0) x).re =
      (c : ℝ) * (a : ℝ) / (1 - (a : ℝ) * x) := by
  have hd : barrierTailLinearDen (barrierComplex a 0) x =
      ((1 - (a : ℝ) * x : ℝ) : ℂ) := by
    simp only [barrierTailLinearDen, barrierComplex_real, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_mul]
    ring
  rw [hd]
  simp only [barrierComplex_real, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re]

private theorem barrier_realTailQuadratic_re (a c : ℚ) (x : ℝ) :
    (barrierComplex c 0 * barrierComplex a 0 /
      barrierTailQuadraticDen (barrierComplex a 0) x).re =
      (c : ℝ) * (a : ℝ) / (1 - 2 * (a : ℝ) * x + (a : ℝ) ^ 2) := by
  have hd : barrierTailQuadraticDen (barrierComplex a 0) x =
      ((1 - 2 * (a : ℝ) * x + (a : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp only [barrierTailQuadraticDen, barrierComplex_real, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_pow]
    ring
  rw [hd]
  simp only [barrierComplex_real, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re]

private theorem barrier_list_map_sum_re {α : Type*} (rs : List α)
    (f : α → ℂ) (g : α → ℝ) (h : ∀ a, (f a).re = g a) :
    (rs.map f).sum.re = (rs.map g).sum := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re, h a, ih]

private theorem barrier_list_flatMap_sum_re {α : Type*} (rs : List α)
    (expand : α → List (ℂ × ℂ)) (f : ℂ × ℂ → ℂ) (g : α → ℝ)
    (h : ∀ a, ((expand a).map f).sum.re = g a) :
    ((rs.flatMap expand).map f).sum.re = (rs.map g).sum := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, Complex.add_re,
      List.map_cons, List.sum_cons, h a, ih]

private theorem barrier_grouped_tail_sum_re (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (f : ℂ × ℂ → ℂ)
    (g : ℚ × ℚ → ℝ) (h : BarrierRationalPairRow → ℝ)
    (hreal : ∀ ac : ℚ × ℚ,
      (f (barrierComplex ac.1 0, barrierComplex ac.2 0)).re = g ac)
    (hpair : ∀ row : BarrierRationalPairRow,
      ((barrierExpandPairRow row).map f).sum.re = h row) :
    ((barrierExpandRealRows rs ++ barrierExpandPairRows ps).map f).sum.re =
      (rs.map g).sum + (ps.map h).sum := by
  have hr : ((barrierExpandRealRows rs).map f).sum.re = (rs.map g).sum := by
    simpa only [barrierExpandRealRows, List.map_map, Function.comp_def] using
      barrier_list_map_sum_re rs
        (fun ac : ℚ × ℚ => f (barrierComplex ac.1 0, barrierComplex ac.2 0)) g hreal
  have hp : ((barrierExpandPairRows ps).map f).sum.re = (ps.map h).sum := by
    simpa only [barrierExpandPairRows] using
      barrier_list_flatMap_sum_re ps barrierExpandPairRow f h hpair
  rw [List.map_append, List.sum_append, Complex.add_re, hr, hp]

theorem barrierP2Tail_quadratic_sum_re_eq_grouped (x : ℝ) :
    (barrierP2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      barrierGroupedQuadraticTailValue barrierP2RealRows barrierP2PairRows x := by
  rw [barrierP2Tail_eq_grouped]
  unfold barrierGroupedQuadraticTailValue
  apply barrier_grouped_tail_sum_re
  · intro ac
    exact barrier_realTailQuadratic_re ac.1 ac.2 x
  · intro row
    exact barrierConjugatePair_quadratic_eq_ratPolynomial row.a row.b row.c row.d x

theorem barrierV2Tail_linear_sum_re_eq_grouped (x : ℝ) :
    (barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re =
      barrierGroupedLinearTailValue barrierV2RealRows barrierV2PairRows x := by
  rw [barrierV2Tail_eq_grouped]
  unfold barrierGroupedLinearTailValue
  apply barrier_grouped_tail_sum_re
  · intro ac
    exact barrier_realTailLinear_re ac.1 ac.2 x
  · intro row
    exact barrierConjugatePair_linear_eq_ratPolynomial row.a row.b row.c row.d x

theorem barrierV2Tail_quadratic_sum_re_eq_grouped (x : ℝ) :
    (barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      barrierGroupedQuadraticTailValue barrierV2RealRows barrierV2PairRows x := by
  rw [barrierV2Tail_eq_grouped]
  unfold barrierGroupedQuadraticTailValue
  apply barrier_grouped_tail_sum_re
  · intro ac
    exact barrier_realTailQuadratic_re ac.1 ac.2 x
  · intro row
    exact barrierConjugatePair_quadratic_eq_ratPolynomial row.a row.b row.c row.d x

def barrierLinearFractions (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : List (ℚ[X] × ℚ[X]) :=
  rs.map (fun ac : ℚ × ℚ => (C (ac.2 * ac.1), barrierRealLinearQ ac.1)) ++
    ps.map (fun row : BarrierRationalPairRow =>
      (barrierPairLinearA row.a row.b row.c row.d, barrierPairLinearQ row.a row.b))

def barrierQuadraticFractions (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : List (ℚ[X] × ℚ[X]) :=
  rs.map (fun ac : ℚ × ℚ => (C (ac.2 * ac.1), barrierRealQuadraticQ ac.1)) ++
    ps.map (fun row : BarrierRationalPairRow =>
      (barrierPairQuadraticA row.a row.b row.c row.d, barrierPairQuadraticQ row.a row.b))

def barrierScaleFractions (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) : List (ℚ[X] × ℚ[X]) :=
  fs.map (fun aq : ℚ[X] × ℚ[X] => (C c * aq.1, aq.2))

private theorem barrierLinearFractions_product (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) :
    barrierFractionProduct (barrierLinearFractions rs ps) = barrierGroupedLinearQ rs ps := by
  simp [barrierFractionProduct, barrierLinearFractions, barrierGroupedLinearQ,
    List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem barrierQuadraticFractions_product (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) :
    barrierFractionProduct (barrierQuadraticFractions rs ps) = barrierGroupedQuadraticQ rs ps := by
  simp [barrierFractionProduct, barrierQuadraticFractions, barrierGroupedQuadraticQ,
    List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem barrierFractionProduct_append (fs gs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (fs ++ gs) = barrierFractionProduct fs * barrierFractionProduct gs := by
  simp [barrierFractionProduct, List.map_append, List.prod_append]

private theorem barrierScaleFractions_product (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (barrierScaleFractions c fs) = barrierFractionProduct fs := by
  simp [barrierFractionProduct, barrierScaleFractions, List.map_map, Function.comp_def]

private theorem barrierLinearFractions_sum (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    barrierFractionSum (barrierLinearFractions rs ps) x =
      barrierGroupedLinearTailValue rs ps x := by
  simp [barrierFractionSum, barrierLinearFractions, barrierGroupedLinearTailValue,
    barrierRealLinearQ, List.map_append, List.sum_append, List.map_map, Function.comp_def]

private theorem barrierQuadraticFractions_sum (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    barrierFractionSum (barrierQuadraticFractions rs ps) x =
      barrierGroupedQuadraticTailValue rs ps x := by
  simp [barrierFractionSum, barrierQuadraticFractions, barrierGroupedQuadraticTailValue,
    barrierRealQuadraticQ, eval₂_pow, List.map_append, List.sum_append, List.map_map, Function.comp_def]

private theorem barrierFractionSum_append (fs gs : List (ℚ[X] × ℚ[X])) (x : ℝ) :
    barrierFractionSum (fs ++ gs) x = barrierFractionSum fs x + barrierFractionSum gs x := by
  simp [barrierFractionSum, List.map_append, List.sum_append]

private theorem barrierScaleFractions_sum (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) (x : ℝ) :
    barrierFractionSum (barrierScaleFractions c fs) x = (c : ℝ) * barrierFractionSum fs x := by
  simpa only [barrierFractionSum, barrierScaleFractions, List.map_map, Function.comp_def,
    eval₂_mul, eval₂_C, Rat.coe_castHom, mul_div_assoc] using
    List.sum_map_mul_left fs
      (fun aq : ℚ[X] × ℚ[X] =>
        aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x) (c : ℝ)

def barrierCase2XFractions : List (ℚ[X] × ℚ[X]) :=
  [(C (19 / 48), X), (-C (1 / 12), 1 - X), (-C (65 / 24) * X, 1 + X ^ 2),
   (-(C 4 * barrierFiniteUDerivative barrierP2Finite +
       barrierFinitePowerDerivative barrierV2Finite), 1)] ++
  barrierScaleFractions (-4) (barrierQuadraticFractions barrierP2RealRows barrierP2PairRows) ++
  barrierScaleFractions (-1) (barrierLinearFractions barrierV2RealRows barrierV2PairRows)

def barrierCase2YFractions : List (ℚ[X] × ℚ[X]) :=
  [(C (7 / 48), X), (-C (1 / 12), 1 - X),
   (C 2 * barrierFiniteUDerivative barrierV2Finite, 1)] ++
  barrierScaleFractions 2 (barrierQuadraticFractions barrierV2RealRows barrierV2PairRows)

def barrierCase2XDerivativeFormula (x : ℝ) : ℝ :=
  (19 / 48) / x - (1 / 12) / (1 - x) - (65 / 24) * x / (1 + x ^ 2) -
    4 * ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierP2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) -
    ((barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re)

def barrierCase2YDerivativeFormula (x : ℝ) : ℝ :=
  (7 / 48) / x - (1 / 12) / (1 - x) +
    2 * ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)

theorem barrierCase2XFractions_product :
    barrierFractionProduct barrierCase2XFractions = barrierCase2QX := by
  simp only [barrierCase2XFractions, barrierFractionProduct_append,
    barrierScaleFractions_product, barrierLinearFractions_product,
    barrierQuadraticFractions_product]
  simp only [barrierFractionProduct, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, barrierCase2QX, barrierP2QuadraticQ, barrierV2LinearQ]
  ring

theorem barrierCase2YFractions_product :
    barrierFractionProduct barrierCase2YFractions = barrierCase2QY := by
  simp only [barrierCase2YFractions, barrierFractionProduct_append,
    barrierScaleFractions_product, barrierQuadraticFractions_product]
  simp only [barrierFractionProduct, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, barrierCase2QY, barrierV2QuadraticQ]

theorem barrierCase2XFractions_sum (x : ℝ) :
    barrierFractionSum barrierCase2XFractions x = barrierCase2XDerivativeFormula x := by
  simp only [barrierCase2XFractions, barrierFractionSum_append, barrierScaleFractions_sum,
    barrierLinearFractions_sum, barrierQuadraticFractions_sum]
  unfold barrierCase2XDerivativeFormula
  rw [barrierP2Tail_quadratic_sum_re_eq_grouped, barrierV2Tail_linear_sum_re_eq_grouped]
  norm_num [barrierFractionSum, eval₂_pow]
  ring

theorem barrierCase2YFractions_sum (x : ℝ) :
    barrierFractionSum barrierCase2YFractions x = barrierCase2YDerivativeFormula x := by
  simp only [barrierCase2YFractions, barrierFractionSum_append, barrierScaleFractions_sum,
    barrierQuadraticFractions_sum]
  unfold barrierCase2YDerivativeFormula
  rw [barrierV2Tail_quadratic_sum_re_eq_grouped]
  norm_num [barrierFractionSum]
  ring

def barrierCase2AX : ℚ[X] := barrierFractionNumerator barrierCase2XFractions
def barrierCase2AY : ℚ[X] := barrierFractionNumerator barrierCase2YFractions

theorem barrierCase2AX_clears_denominator {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    barrierCase2AX.eval₂ (Rat.castHom ℝ) x =
      barrierCase2QX.eval₂ (Rat.castHom ℝ) x * barrierCase2XDerivativeFormula x := by
  have hprod : (barrierFractionProduct barrierCase2XFractions).eval₂ (Rat.castHom ℝ) x ≠ 0 := by
    rw [barrierCase2XFractions_product]
    exact barrierCase2QX_eval_ne_zero hx hx0 hx1
  simpa only [barrierCase2AX, barrierCase2XFractions_product, barrierCase2XFractions_sum] using
    barrierFractionNumerator_eval barrierCase2XFractions x hprod

theorem barrierCase2AY_clears_denominator {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    barrierCase2AY.eval₂ (Rat.castHom ℝ) x =
      barrierCase2QY.eval₂ (Rat.castHom ℝ) x * barrierCase2YDerivativeFormula x := by
  have hprod : (barrierFractionProduct barrierCase2YFractions).eval₂ (Rat.castHom ℝ) x ≠ 0 := by
    rw [barrierCase2YFractions_product]
    exact barrierCase2QY_eval_ne_zero hx hx0 hx1
  simpa only [barrierCase2AY, barrierCase2YFractions_product, barrierCase2YFractions_sum] using
    barrierFractionNumerator_eval barrierCase2YFractions x hprod

def barrierCase2AYExplicit : ℚ[X] :=
  C (6139400617553994264158059821657057/46566128730773925781250000000000000000000) +
  C (-33561002014090297827119379306520481903587029/2328306436538696289062500000000000000000000000000) * X ^ 1 +
  C (33074408368087250152306475891437531860945477517/55879354476928710937500000000000000000000000000000) * X ^ 2 +
  C (-66077599258590392372719123938575511970776167147/3725290298461914062500000000000000000000000000000) * X ^ 3 +
  C (14122789091810067197857825223683987234653915605963/27939677238464355468750000000000000000000000000000) * X ^ 4 +
  C (-86750624167723639733042199688839383716982023693179/9313225746154785156250000000000000000000000000000) * X ^ 5 +
  C (1316740050792652908780607827887161749864672742734289/13969838619232177734375000000000000000000000000000) * X ^ 6 +
  C (-1212115504788431760218102810891669598130270751340433/2328306436538696289062500000000000000000000000000) * X ^ 7 +
  C (1852388549149144304739559910201030352481292410036837/1164153218269348144531250000000000000000000000000) * X ^ 8 +
  C (-1747032160720335963573846025320381769579591080592813/582076609134674072265625000000000000000000000000) * X ^ 9 +
  C (1739901547181074548477858628301501635372218788391207/291038304567337036132812500000000000000000000000) * X ^ 10 +
  C (-58398556052369231733549806414095197880896863913593/4547473508864641189575195312500000000000000000) * X ^ 11 +
  C (-224485494639452816006183298746436192812684184457/227373675443232059478759765625000000000000000) * X ^ 12 +
  C (2269599238587048364445509906643305862019685574511/29103830456733703613281250000000000000000000) * X ^ 13 +
  C (-8312207244243935884298339203836978265449226071511/72759576141834259033203125000000000000000000) * X ^ 14 +
  C (-378061677768450552949892491615489728857434329461/3637978807091712951660156250000000000000000) * X ^ 15 +
  C (6336754667545200773744815681065942607080067871/18189894035458564758300781250000000000000) * X ^ 16 +
  C (-23670761651501264423340946642925921358111/355271367880050092935562133789062500) * X ^ 17 +
  C (-1591316942855983330678136272429722751753611/3637978807091712951660156250000000000) * X ^ 18 +
  C (2196441555444677056714374493311795175923/7275957614183425903320312500000000) * X ^ 19 +
  C (19920658548966767554832955780992945163/90949470177292823791503906250000) * X ^ 20 +
  C (-252630662688341342631694749106212633/909494701772928237915039062500) * X ^ 21 +
  C (8040903690975846553048561271748/1818989403545856475830078125) * X ^ 22 +
  C (1234121953779801858851339053248/14551915228366851806640625) * X ^ 23 +
  C (-3121113626614610031471086592/116415321826934814453125) * X ^ 24

private theorem barrier_case2_U_3 :
    Chebyshev.U ℚ 3 = 2 * X * Chebyshev.U ℚ 2 - Chebyshev.U ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 1

private theorem barrier_case2_U_4 :
    Chebyshev.U ℚ 4 = 2 * X * Chebyshev.U ℚ 3 - Chebyshev.U ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 2

private theorem barrier_case2_U_5 :
    Chebyshev.U ℚ 5 = 2 * X * Chebyshev.U ℚ 4 - Chebyshev.U ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 3

private theorem barrier_case2_U_6 :
    Chebyshev.U ℚ 6 = 2 * X * Chebyshev.U ℚ 5 - Chebyshev.U ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 4

private theorem barrier_case2_U_7 :
    Chebyshev.U ℚ 7 = 2 * X * Chebyshev.U ℚ 6 - Chebyshev.U ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 5

private theorem barrier_case2_U_8 :
    Chebyshev.U ℚ 8 = 2 * X * Chebyshev.U ℚ 7 - Chebyshev.U ℚ 6 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 6

private theorem barrier_case2_U_9 :
    Chebyshev.U ℚ 9 = 2 * X * Chebyshev.U ℚ 8 - Chebyshev.U ℚ 7 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 7

theorem barrierCase2AY_eq_explicit : barrierCase2AY = barrierCase2AYExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2AY, barrierCase2AYExplicit, barrierFractionNumerator,
    barrierFractionProduct, barrierCase2YFractions, barrierScaleFractions,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    barrierFiniteUDerivative, barrierFinitePowerDerivative, barrierP2Finite, barrierV2Finite,
    Finset.sum_range_succ, eval_finsetSum, eval_list_prod,
    Chebyshev.U_two, barrier_case2_U_3, barrier_case2_U_4,
    barrier_case2_U_5, barrier_case2_U_6, barrier_case2_U_7,
    barrier_case2_U_8, barrier_case2_U_9]
  ring

theorem barrierCase2AY_natDegree : barrierCase2AY.natDegree = 24 := by
  rw [barrierCase2AY_eq_explicit]
  unfold barrierCase2AYExplicit
  compute_degree!

def barrierCase2AXExplicit : ℚ[X] :=
  C (30307837230416268959058568549773/390625000000000000000000000000000000) +
  C (-388916241323180816905894669551174674670591/1220703125000000000000000000000000000000000000) * X ^ 1 +
  C (-4006784573305776602421578075882271527736951993/1220703125000000000000000000000000000000000000000) * X ^ 2 +
  C (1096183954671168725038063556149715387207630523987/61035156250000000000000000000000000000000000000000) * X ^ 3 +
  C (-7952498478159654485025286927264757800766806449689461/91552734375000000000000000000000000000000000000000000) * X ^ 4 +
  C (-173251421552630457395123417783409511688090895941195417/4577636718750000000000000000000000000000000000000000000) * X ^ 5 +
  C (1222120559292925857030215856817101460328272419116765158471/228881835937500000000000000000000000000000000000000000000) * X ^ 6 +
  C (-9002153638868141433199303807358329862172831171827356580769/762939453125000000000000000000000000000000000000000000000) * X ^ 7 +
  C (-20430716055979141452221343027896515893162803128568450962685989/286102294921875000000000000000000000000000000000000000000000) * X ^ 8 +
  C (1551532006333267422675951782124692841597537382079615796002800463/7152557373046875000000000000000000000000000000000000000000000) * X ^ 9 +
  C (3430606054133072949419772876756861170914507767290711053103959413/11920928955078125000000000000000000000000000000000000000000000) * X ^ 10 +
  C (-505916145739811163969788025388361352785579438858951141108745471259/357627868652343750000000000000000000000000000000000000000000000) * X ^ 11 +
  C (170660418192088844983109244182859397071662139279111654553014694589/357627868652343750000000000000000000000000000000000000000000000) * X ^ 12 +
  C (111802796781702066809285191673959138398105580484717994246462464509/37252902984619140625000000000000000000000000000000000000000000) * X ^ 13 +
  C (-45027051395514975383376671261049412207657650433594188527438870439467/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 14 +
  C (16509003686870615770955343186283294035863361608791696629553878592691/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 15 +
  C (39466767544097375649642054097024548875637201165892323429352340271739/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 16 +
  C (-26755287098024999828824584679516056137747845043276649132658782483257/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 17 +
  C (168070108726307711595570993536980340222190659762943286668833668339249/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 18 +
  C (-832051437619875563928237488265539747452368600303675116627132838151/596046447753906250000000000000000000000000000000000000000000000) * X ^ 19 +
  C (-1606955218748669940170405173174994300085549469536010604897519048427/74505805969238281250000000000000000000000000000000000000000000) * X ^ 20 +
  C (2433137840814792444702356102800877012295375212980653188941121382049/59604644775390625000000000000000000000000000000000000000000000) * X ^ 21 +
  C (-51739167878202129506248629638529892446087925833524235401379411247437/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 22 +
  C (-1082632152122822888597045006113490327710626764705887378288008787721/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 23 +
  C (4986802693523860777269281537299839923932961413477019773621637642489/149011611938476562500000000000000000000000000000000000000000000) * X ^ 24 +
  C (-4416319363306657399702427900939605066393368736600070485184725132417/93132257461547851562500000000000000000000000000000000000000000) * X ^ 25 +
  C (430725170281186155782445052791711482276044238852484890595621567703/11641532182693481445312500000000000000000000000000000000000000) * X ^ 26 +
  C (-5858283778532255307754122045950281887663478271777393285415699291/1164153218269348144531250000000000000000000000000000000000000) * X ^ 27 +
  C (-9526115897201306594135430784633925777531015543666247018754883/465661287307739257812500000000000000000000000000000000000) * X ^ 28 +
  C (627455201464947631518402076531001458986822444066613529731827/23283064365386962890625000000000000000000000000000000000) * X ^ 29 +
  C (-1505504840851826080906317395924633616756101528774509886831583/72759576141834259033203125000000000000000000000000000000) * X ^ 30 +
  C (6417086791213399557054520364584799762086047849866994798447/909494701772928237915039062500000000000000000000000000) * X ^ 31 +
  C (463404787046380243295539802625032027305554181181839276149/145519152283668518066406250000000000000000000000000000) * X ^ 32 +
  C (-79635932674577498395062383173973277954089807724779169/14551915228366851806640625000000000000000000000000) * X ^ 33 +
  C (306952565700894986183323747480996064114191827407661/72759576141834259033203125000000000000000000000) * X ^ 34 +
  C (-29493660039437141081639612350479227384504308233/14551915228366851806640625000000000000000000) * X ^ 35 +
  C (60188546402546646873910140358666064623915029/145519152283668518066406250000000000000000) * X ^ 36

def barrierCase2AXCoefficient (k : ℕ) : ℚ :=
  ([30307837230416268959058568549773/390625000000000000000000000000000000, -388916241323180816905894669551174674670591/1220703125000000000000000000000000000000000000, -4006784573305776602421578075882271527736951993/1220703125000000000000000000000000000000000000000, 1096183954671168725038063556149715387207630523987/61035156250000000000000000000000000000000000000000, -7952498478159654485025286927264757800766806449689461/91552734375000000000000000000000000000000000000000000, -173251421552630457395123417783409511688090895941195417/4577636718750000000000000000000000000000000000000000000, 1222120559292925857030215856817101460328272419116765158471/228881835937500000000000000000000000000000000000000000000, -9002153638868141433199303807358329862172831171827356580769/762939453125000000000000000000000000000000000000000000000, -20430716055979141452221343027896515893162803128568450962685989/286102294921875000000000000000000000000000000000000000000000, 1551532006333267422675951782124692841597537382079615796002800463/7152557373046875000000000000000000000000000000000000000000000, 3430606054133072949419772876756861170914507767290711053103959413/11920928955078125000000000000000000000000000000000000000000000, -505916145739811163969788025388361352785579438858951141108745471259/357627868652343750000000000000000000000000000000000000000000000, 170660418192088844983109244182859397071662139279111654553014694589/357627868652343750000000000000000000000000000000000000000000000, 111802796781702066809285191673959138398105580484717994246462464509/37252902984619140625000000000000000000000000000000000000000000, -45027051395514975383376671261049412207657650433594188527438870439467/8940696716308593750000000000000000000000000000000000000000000000, 16509003686870615770955343186283294035863361608791696629553878592691/4470348358154296875000000000000000000000000000000000000000000000, 39466767544097375649642054097024548875637201165892323429352340271739/8940696716308593750000000000000000000000000000000000000000000000, -26755287098024999828824584679516056137747845043276649132658782483257/1490116119384765625000000000000000000000000000000000000000000000, 168070108726307711595570993536980340222190659762943286668833668339249/8940696716308593750000000000000000000000000000000000000000000000, -832051437619875563928237488265539747452368600303675116627132838151/596046447753906250000000000000000000000000000000000000000000000, -1606955218748669940170405173174994300085549469536010604897519048427/74505805969238281250000000000000000000000000000000000000000000, 2433137840814792444702356102800877012295375212980653188941121382049/59604644775390625000000000000000000000000000000000000000000000, -51739167878202129506248629638529892446087925833524235401379411247437/1490116119384765625000000000000000000000000000000000000000000000, -1082632152122822888597045006113490327710626764705887378288008787721/1490116119384765625000000000000000000000000000000000000000000000, 4986802693523860777269281537299839923932961413477019773621637642489/149011611938476562500000000000000000000000000000000000000000000, -4416319363306657399702427900939605066393368736600070485184725132417/93132257461547851562500000000000000000000000000000000000000000, 430725170281186155782445052791711482276044238852484890595621567703/11641532182693481445312500000000000000000000000000000000000000, -5858283778532255307754122045950281887663478271777393285415699291/1164153218269348144531250000000000000000000000000000000000000, -9526115897201306594135430784633925777531015543666247018754883/465661287307739257812500000000000000000000000000000000000, 627455201464947631518402076531001458986822444066613529731827/23283064365386962890625000000000000000000000000000000000, -1505504840851826080906317395924633616756101528774509886831583/72759576141834259033203125000000000000000000000000000000, 6417086791213399557054520364584799762086047849866994798447/909494701772928237915039062500000000000000000000000000, 463404787046380243295539802625032027305554181181839276149/145519152283668518066406250000000000000000000000000000, -79635932674577498395062383173973277954089807724779169/14551915228366851806640625000000000000000000000000, 306952565700894986183323747480996064114191827407661/72759576141834259033203125000000000000000000000, -29493660039437141081639612350479227384504308233/14551915228366851806640625000000000000000000, 60188546402546646873910140358666064623915029/145519152283668518066406250000000000000000] : List ℚ).getD k 0

def barrierCase2PTailNumeratorExplicit : ℚ[X] :=
  C (-334625418567286147906955121183793659/4882812500000000000000000000000000000000) +
  C (20127644970984429229663641286102109817/12207031250000000000000000000000000000000) * X ^ 1 +
  C (-2852876572408096311386663148074363127/610351562500000000000000000000000000000) * X ^ 2 +
  C (219782662978769686811412440485306881/3051757812500000000000000000000000000) * X ^ 3 +
  C (-4894248692719660966896600643752953/19073486328125000000000000000000000) * X ^ 4 +
  C (45491985122617474473894836809089153/15258789062500000000000000000000000) * X ^ 5 +
  C (-568781315379457100097709309340883/30517578125000000000000000000000) * X ^ 6 +
  C (803074381853681639161748844303/7629394531250000000000000000) * X ^ 7 +
  C (-5453962494228714418500320647/30517578125000000000000000) * X ^ 8 +
  C (680879861223820138383153/7629394531250000000000) * X ^ 9

def barrierCase2PTailProductExplicit : ℚ[X] :=
  C (4785447983749937204061879244701/24414062500000000000000000000000000) +
  C (-474962018866734369442083826221/1220703125000000000000000000000000) * X ^ 1 +
  C (7705227818365150047259368501/2441406250000000000000000000000) * X ^ 2 +
  C (-3589839094005450574517959947/610351562500000000000000000000) * X ^ 3 +
  C (84481480701896139333127067089/152587890625000000000000000000) * X ^ 4 +
  C (-8340696096348800303572388719/7629394531250000000000000000) * X ^ 5 +
  C (2527238180877059028537517647/76293945312500000000000000) * X ^ 6 +
  C (-1973789704813765919735753/30517578125000000000000) * X ^ 7 +
  C (37686962338137420137757/152587890625000000000) * X ^ 8 +
  C (-13017638552052412621/30517578125000000) * X ^ 9 +
  C (32299425202362199/152587890625000) * X ^ 10

theorem barrierCase2PTailNumerator_eq_explicit :
    barrierFractionNumerator (barrierQuadraticFractions barrierP2RealRows barrierP2PairRows) = barrierCase2PTailNumeratorExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2PTailNumeratorExplicit, barrierFractionNumerator, barrierFractionProduct,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    eval_list_prod]
  ring

theorem barrierCase2PTailProduct_eq_explicit :
    barrierFractionProduct (barrierQuadraticFractions barrierP2RealRows barrierP2PairRows) = barrierCase2PTailProductExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2PTailProductExplicit, barrierFractionNumerator, barrierFractionProduct,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    eval_list_prod]
  ring

def barrierCase2AYCoefficient (k : ℕ) : ℚ :=
  ([6139400617553994264158059821657057/46566128730773925781250000000000000000000, -33561002014090297827119379306520481903587029/2328306436538696289062500000000000000000000000000, 33074408368087250152306475891437531860945477517/55879354476928710937500000000000000000000000000000, -66077599258590392372719123938575511970776167147/3725290298461914062500000000000000000000000000000, 14122789091810067197857825223683987234653915605963/27939677238464355468750000000000000000000000000000, -86750624167723639733042199688839383716982023693179/9313225746154785156250000000000000000000000000000, 1316740050792652908780607827887161749864672742734289/13969838619232177734375000000000000000000000000000, -1212115504788431760218102810891669598130270751340433/2328306436538696289062500000000000000000000000000, 1852388549149144304739559910201030352481292410036837/1164153218269348144531250000000000000000000000000, -1747032160720335963573846025320381769579591080592813/582076609134674072265625000000000000000000000000, 1739901547181074548477858628301501635372218788391207/291038304567337036132812500000000000000000000000, -58398556052369231733549806414095197880896863913593/4547473508864641189575195312500000000000000000, -224485494639452816006183298746436192812684184457/227373675443232059478759765625000000000000000, 2269599238587048364445509906643305862019685574511/29103830456733703613281250000000000000000000, -8312207244243935884298339203836978265449226071511/72759576141834259033203125000000000000000000, -378061677768450552949892491615489728857434329461/3637978807091712951660156250000000000000000, 6336754667545200773744815681065942607080067871/18189894035458564758300781250000000000000, -23670761651501264423340946642925921358111/355271367880050092935562133789062500, -1591316942855983330678136272429722751753611/3637978807091712951660156250000000000, 2196441555444677056714374493311795175923/7275957614183425903320312500000000, 19920658548966767554832955780992945163/90949470177292823791503906250000, -252630662688341342631694749106212633/909494701772928237915039062500, 8040903690975846553048561271748/1818989403545856475830078125, 1234121953779801858851339053248/14551915228366851806640625, -3121113626614610031471086592/116415321826934814453125] : List ℚ).getD k 0

private theorem barrierCase2AY_eval_quarter_ne_zero :
    barrierCase2AY.eval (1 / 4) ≠ 0 := by
  rw [barrierCase2AY_eq_explicit]
  norm_num [barrierCase2AYExplicit, eval_pow]

private theorem barrierCase2AY_eval_half_ne_zero :
    barrierCase2AY.eval (1 / 2) ≠ 0 := by
  rw [barrierCase2AY_eq_explicit]
  norm_num [barrierCase2AYExplicit, eval_pow]

private theorem barrierCase2AY_eval_three_quarters_ne_zero :
    barrierCase2AY.eval (3 / 4) ≠ 0 := by
  rw [barrierCase2AY_eq_explicit]
  norm_num [barrierCase2AYExplicit, eval_pow]

theorem barrierCase2AY_quarter_nonzero :
    barrierCase2AY.eval (1 / 4) ≠ 0 ∧
      barrierCase2AY.eval (1 / 2) ≠ 0 ∧
      barrierCase2AY.eval (3 / 4) ≠ 0 := by
  exact ⟨barrierCase2AY_eval_quarter_ne_zero, barrierCase2AY_eval_half_ne_zero,
    barrierCase2AY_eval_three_quarters_ne_zero⟩

theorem barrierCase2AXExplicit_coeff_35 :
    barrierCase2AXExplicit.coeff 35 = barrierCase2AXCoefficient 35 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_36 :
    barrierCase2AXExplicit.coeff 36 = barrierCase2AXCoefficient 36 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

end InternalCatalan

end

end OAI
