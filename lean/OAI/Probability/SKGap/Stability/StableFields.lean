import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix
namespace SKGap

abbrev Field (n : ℕ) := Fin n → ℝ

def magnetization {n : ℕ} (y : Field n) : Field n := fun i => tanh (y i)
def overlap {n : ℕ} (y : Field n) : ℝ := (∑ i, magnetization y i ^ 2) / n
def onsager {n : ℕ} (j : ℝ) (y : Field n) : ℝ := j * (1 - overlap y)
def spinVariance {n : ℕ} (y : Field n) : Field n := fun i => 1 - magnetization y i ^ 2

def tapField {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : Field n := fun i =>
  y i - h i + onsager j y * magnetization y i - ∑ k, J i k * magnetization y k

def hessianCore {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y : Field n) : Matrix (Fin n) (Fin n) ℝ := fun i k =>
  onsager j y * (if i = k then 1 else 0) - J i k -
    (2 * j / n) * magnetization y i * magnetization y k

def fieldHessian {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y A : Field n) : Matrix (Fin n) (Fin n) ℝ := fun i k =>
  (if i = k then 1 else 0) + sqrt (A i) * hessianCore j J y i k * sqrt (A k)

def vectorSqNorm {n : ℕ} (x : Field n) : ℝ := ∑ i, x i ^ 2

def quadraticForm {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (x : Field n) : ℝ :=
  ∑ i, ∑ k, x i * J i k * x k

theorem overlap_nonneg {n : ℕ} (y : Field n) : 0 ≤ overlap y :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem overlap_lt_one {n : ℕ} (hn : 0 < n) (y : Field n) : overlap y < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_lt_iff₀ hn').mpr
  simp only [one_mul]
  calc
    (∑ i, magnetization y i ^ 2) < ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
      · intro i _
        exact tanh_sq_lt_one (y i)
    _ = n := by simp

theorem spinVariance_pos {n : ℕ} (y : Field n) (i : Fin n) :
    0 < spinVariance y i := sub_pos.mpr (tanh_sq_lt_one _)

theorem spinVariance_le_one {n : ℕ} (y : Field n) (i : Fin n) :
    spinVariance y i ≤ 1 := sub_le_self _ (sq_nonneg _)

theorem fieldHessian_symm {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : J.IsSymm) (j : ℝ) (y A : Field n) : (fieldHessian j J y A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i k
  simp only [fieldHessian, hessianCore, hJ.apply i k, eq_comm]
  ring

theorem tapField_sub_external {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : tapField j J h y = tapField j J 0 y - h := by
  ext i
  simp only [tapField, Pi.zero_apply, Pi.sub_apply]
  ring

theorem vectorSqNorm_nonneg {n : ℕ} (x : Field n) : 0 ≤ vectorSqNorm x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem vectorSqNorm_eq_zero {n : ℕ} {x : Field n} : vectorSqNorm x = 0 ↔ x = 0 := by
  unfold vectorSqNorm
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, sq_eq_zero_iff, funext_iff, Pi.zero_apply]

theorem hessian_quadratic_formula {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y A x : Field n) :
    quadraticForm (fieldHessian j J y A) x = vectorSqNorm x +
      onsager j y * vectorSqNorm (fun i => sqrt (A i) * x i) -
      quadraticForm J (fun i => sqrt (A i) * x i) -
      (2 * j / n) * (∑ i, magnetization y i * (sqrt (A i) * x i)) ^ 2 := by
  have hi (i : Fin n) :
      (∑ k, x i * fieldHessian j J y A i k * x k) = x i ^ 2 +
        onsager j y * (sqrt (A i) * x i) ^ 2 -
        (∑ k, (sqrt (A i) * x i) * J i k * (sqrt (A k) * x k)) -
        (2 * j / n) * (magnetization y i * (sqrt (A i) * x i)) *
          (∑ k, magnetization y k * (sqrt (A k) * x k)) := by
    calc
      _ = ∑ k, ((if i = k then x i ^ 2 else 0) +
          (if i = k then onsager j y * (sqrt (A i) * x i) ^ 2 else 0) -
          (sqrt (A i) * x i) * J i k * (sqrt (A k) * x k) -
          (2 * j / n) * (magnetization y i * (sqrt (A i) * x i)) *
            (magnetization y k * (sqrt (A k) * x k))) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : i = k
        · subst k
          simp only [fieldHessian, hessianCore, ↓reduceIte]
          ring
        · simp only [fieldHessian, hessianCore, ite_eq_right hk]
          ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
  unfold quadraticForm
  simp_rw [hi]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, vectorSqNorm]
  ring

theorem hessian_lower_bound {n : ℕ} (hn : 0 < n) {j R a : ℝ}
    (hj : 0 ≤ j) {J : Matrix (Fin n) (Fin n) ℝ} (y A : Field n)
    (hA0 : ∀ i, 0 ≤ A i) (hAa : ∀ i, A i ≤ a)
    (hJ : ∀ v : Field n, quadraticForm J v ≤ R * vectorSqNorm v)
    (hcoef : 0 ≤ R - j + 3 * j * overlap y) (x : Field n) :
    (1 - a * (R - j + 3 * j * overlap y)) * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y A) x := by
  let v : Field n := fun i => sqrt (A i) * x i
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (∑ i, magnetization y i ^ 2) = n * overlap y := by
    unfold overlap
    field_simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (magnetization y) v
  rw [hm] at hcs
  have hscale : 0 ≤ 2 * j / (n : ℝ) := by positivity
  have hrank : (2 * j / n) * (∑ i, magnetization y i * v i) ^ 2 ≤
      2 * j * overlap y * vectorSqNorm v := by
    have he : (2 * j / n) * ((n : ℝ) * overlap y * vectorSqNorm v) =
        2 * j * overlap y * vectorSqNorm v := by field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_left hcs hscale
  have hv : vectorSqNorm v ≤ a * vectorSqNorm x := by
    rw [vectorSqNorm, vectorSqNorm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    dsimp [v]
    rw [mul_pow, sq_sqrt (hA0 i)]
    exact mul_le_mul_of_nonneg_right (hAa i) (sq_nonneg _)
  rw [hessian_quadratic_formula]
  change (1 - a * (R - j + 3 * j * overlap y)) * vectorSqNorm x ≤
    vectorSqNorm x + onsager j y * vectorSqNorm v - quadraticForm J v -
      (2 * j / n) * (∑ i, magnetization y i * v i) ^ 2
  have hmul := mul_le_mul_of_nonneg_left hv hcoef
  dsimp [onsager]
  nlinarith [hJ v, hrank]

def fieldJacobian {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y : Field n) : Matrix (Fin n) (Fin n) ℝ := fun i k =>
  (if i = k then 1 else 0) + hessianCore j J y i k * spinVariance y k

theorem hasDerivAt_tanh (y : ℝ) : HasDerivAt tanh (1 - tanh y ^ 2) y := by
  convert! (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (cosh_pos y).ne' using 1
  · ext x
    exact tanh_eq_sinh_div_cosh x
  · rw [tanh_eq_sinh_div_cosh]
    field_simp

theorem magnetization_hasFDerivAt {n : ℕ} (y : Field n) (i : Fin n) :
    HasFDerivAt (fun z : Field n => magnetization z i)
      (spinVariance y i • (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y :=
  (hasDerivAt_tanh (y i)).comp_hasFDerivAt y (hasFDerivAt_apply i y)

def overlapDerivative {n : ℕ} (y : Field n) : Field n →L[ℝ] ℝ :=
  (2 / (n : ℝ)) • ∑ k, (magnetization y k * spinVariance y k) • ContinuousLinearMap.proj k

theorem overlap_hasFDerivAt {n : ℕ} (y : Field n) :
    HasFDerivAt overlap (overlapDerivative y) y := by
  have hd := (HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).pow 2)).const_mul (n : ℝ)⁻¹
  convert! hd using 1
  · ext z
    simp only [overlap, Finset.sum_apply, div_eq_mul_inv]
    ring
  · ext v
    simp only [overlapDerivative, _root_.smul_apply,
      _root_.sum_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      nsmul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem onsager_hasFDerivAt {n : ℕ} (j : ℝ) (y : Field n) :
    HasFDerivAt (onsager j) (-j • overlapDerivative y) y := by
  convert! ((overlap_hasFDerivAt y).const_sub 1).const_mul j using 1
  ext v
  simp only [_root_.smul_apply, smul_eq_mul, _root_.neg_apply]
  ring

theorem tapField_hasFDerivAt {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    HasFDerivAt (tapField j J h)
      ((fieldJacobian j J y).mulVecLin.toContinuousLinearMap) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hfirst := ((hasFDerivAt_apply i y).sub_const (h i)).add
    ((onsager_hasFDerivAt j y).mul (magnetization_hasFDerivAt y i))
  have hlast := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).const_mul (J i k))
  convert! hfirst.sub hlast using 1
  · ext z
    simp only [tapField, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, fieldJacobian, hessianCore, _root_.sub_apply,
      _root_.add_apply, _root_.smul_apply,
      _root_.sum_apply, smul_eq_mul, overlapDerivative]
    have hdelta : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) = v i := by
      simp
    have hdeltaV : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
        spinVariance y k * v k) = spinVariance y i * v i := by simp
    calc
      _ = (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) +
          onsager j y * (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
            spinVariance y k * v k) -
          (∑ k, J i k * (spinVariance y k * v k)) -
          (2 * j / n) * magnetization y i *
            (∑ k, (magnetization y k * spinVariance y k) * v k) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [hdelta, hdeltaV]
        ring

theorem fieldHessian_variance_intertwine {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y : Field n) (i k : Fin n) :
    fieldHessian j J y (spinVariance y) i k * sqrt (spinVariance y k) =
      sqrt (spinVariance y i) * fieldJacobian j J y i k := by
  have hk := sq_sqrt (spinVariance_pos y k).le
  by_cases hik : i = k
  · subst k
    simp only [fieldHessian, fieldJacobian, ↓reduceIte]
    nlinarith only [congrArg (fun z => sqrt (spinVariance y i) * hessianCore j J y i i * z) hk]
  · simp only [fieldHessian, fieldJacobian, ite_eq_right hik, zero_add]
    nlinarith only [congrArg (fun z => sqrt (spinVariance y i) * hessianCore j J y i k * z) hk]

theorem fieldHessian_variance_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (fieldHessian j J y (spinVariance y)).mulVec
      (fun k => sqrt (spinVariance y k) * v k) =
    fun i => sqrt (spinVariance y i) * (fieldJacobian j J y).mulVec v i := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, fieldHessian_variance_intertwine]
  ring

theorem quadraticForm_eq_dot_mulVec {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℝ) (x : Field n) :
    quadraticForm J x = ∑ i, x i * J.mulVec x i := by
  simp only [quadraticForm, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem jacobian_injective_of_hessian_coercive {n : ℕ} {c j : ℝ} (hc : 0 < c)
    (J : Matrix (Fin n) (Fin n) ℝ) (y : Field n)
    (hH : ∀ x : Field n, c * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    Function.Injective (fieldJacobian j J y).mulVec := by
  apply (fieldJacobian j J y).mulVecLin.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  let w : Field n := fun k => sqrt (spinVariance y k) * v k
  have hw : (fieldHessian j J y (spinVariance y)).mulVec w = 0 := by
    rw [show w = (fun k => sqrt (spinVariance y k) * v k) from rfl,
      fieldHessian_variance_mulVec]
    ext i
    have hi := congrFun hv i
    change (fieldJacobian j J y).mulVec v i = 0 at hi
    change sqrt (spinVariance y i) * (fieldJacobian j J y).mulVec v i = 0
    rw [hi, mul_zero]
  have hquad : quadraticForm (fieldHessian j J y (spinVariance y)) w = 0 := by
    rw [quadraticForm_eq_dot_mulVec, hw]
    simp
  have hn : vectorSqNorm w = 0 := by
    have := hH w
    rw [hquad] at this
    nlinarith [vectorSqNorm_nonneg w]
  have hw0 := vectorSqNorm_eq_zero.mp hn
  ext i
  have hi := congrFun hw0 i
  have hs := sqrt_pos.mpr (spinVariance_pos y i)
  dsimp [w] at hi
  exact (mul_eq_zero.mp hi).resolve_left hs.ne'

def vectorNorm {n : ℕ} (x : Field n) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖

theorem vectorNorm_nonneg {n : ℕ} (x : Field n) : 0 ≤ vectorNorm x := norm_nonneg _

theorem vectorNorm_sq {n : ℕ} (x : Field n) : vectorNorm x ^ 2 = vectorSqNorm x := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

theorem vectorNorm_add_le {n : ℕ} (x z : Field n) :
    vectorNorm (x + z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_sub_le {n : ℕ} (x z : Field n) :
    vectorNorm (x - z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_smul {n : ℕ} (a : ℝ) (x : Field n) :
    vectorNorm (fun i => a * x i) = |a| * vectorNorm x := by
  exact norm_smul a (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))

theorem vector_dot_abs_le {n : ℕ} (x z : Field n) :
    |∑ i, x i * z i| ≤ vectorNorm x * vectorNorm z := by
  simpa only [vectorNorm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    PiLp.toLp_apply, mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_diag_le {n : ℕ} {a : Field n} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, |a i| ≤ M) (x : Field n) :
    vectorNorm (fun i => a i * x i) ≤ M * vectorNorm x := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (mul_nonneg hM (vectorNorm_nonneg _))).mp
  rw [mul_pow, vectorNorm_sq, vectorNorm_sq]
  unfold vectorSqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_pow]
  have hi : a i ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hM).mpr (ha i)
  exact mul_le_mul_of_nonneg_right hi (sq_nonneg (x i))

def sqrtVarianceMul {n : ℕ} (y v : Field n) : Field n :=
  fun i => sqrt (spinVariance y i) * v i

theorem sqrtVarianceMul_norm_le {n : ℕ} (y v : Field n) :
    vectorNorm (sqrtVarianceMul y v) ≤ vectorNorm v := by
  change vectorNorm (fun i => sqrt (spinVariance y i) * v i) ≤ vectorNorm v
  calc
    _ ≤ 1 * vectorNorm v := vectorNorm_diag_le zero_le_one (fun i => by
      rw [abs_of_nonneg (sqrt_nonneg _)]
      exact sqrt_le_one.mpr (spinVariance_le_one y i)) v
    _ = _ := one_mul _

theorem sqrtVarianceMul_twice {n : ℕ} (y v : Field n) :
    sqrtVarianceMul y (sqrtVarianceMul y v) = fun i => spinVariance y i * v i := by
  ext i
  dsimp [sqrtVarianceMul]
  rw [← mul_assoc, mul_self_sqrt (spinVariance_pos y i).le]

theorem weighted_inverse_bound {n : ℕ} {c j : ℝ} (_hc : 0 < c)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hH : ∀ x : Field n, c * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    c * vectorNorm (sqrtVarianceMul y v) ≤
      vectorNorm ((fieldJacobian j J y).mulVec v) := by
  let w := sqrtVarianceMul y v
  let z := (fieldJacobian j J y).mulVec v
  have hi : (fieldHessian j J y (spinVariance y)).mulVec w = sqrtVarianceMul y z :=
    fieldHessian_variance_mulVec j J y v
  have hq := hH w
  rw [quadraticForm_eq_dot_mulVec, hi] at hq
  have hdot := (le_abs_self (∑ i, w i * sqrtVarianceMul y z i)).trans
    (vector_dot_abs_le w (sqrtVarianceMul y z))
  have hz := mul_le_mul_of_nonneg_left (sqrtVarianceMul_norm_le y z) (vectorNorm_nonneg w)
  rw [← vectorNorm_sq] at hq
  change c * vectorNorm w ≤ vectorNorm z
  by_cases hw : vectorNorm w = 0
  · rw [hw, mul_zero]
    exact vectorNorm_nonneg z
  · have hw' : 0 < vectorNorm w := lt_of_le_of_ne (vectorNorm_nonneg w) (Ne.symm hw)
    nlinarith [hq.trans (hdot.trans hz)]

theorem hessianCore_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (hessianCore j J y).mulVec v =
      (fun i => onsager j y * v i) - J.mulVec v -
      (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) * magnetization y i) := by
  ext i
  change (∑ k, hessianCore j J y i k * v k) =
    onsager j y * v i - (∑ k, J i k * v k) -
      ((2 * j / n) * (∑ k, magnetization y k * v k)) * magnetization y i
  calc
    _ = ∑ k, (onsager j y * ((if i = k then 1 else 0) * v k) - J i k * v k -
        ((2 * j / n) * magnetization y i) * (magnetization y k * v k)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [hessianCore]
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
      ring

attribute [local irreducible] vectorNorm

theorem hessianCore_norm_le {n : ℕ} (hn : 0 < n) {j K : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K * vectorNorm z) :
    vectorNorm ((hessianCore j J y).mulVec v) ≤ (K + 3 * j) * vectorNorm v := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 := overlap_nonneg y
  have hq1 := (overlap_lt_one hn y).le
  have hB0 : 0 ≤ onsager j y := mul_nonneg hj (sub_nonneg.mpr hq1)
  have hB : onsager j y ≤ j := by
    dsimp [onsager]
    nlinarith
  have hfirst : vectorNorm (fun i => onsager j y * v i) ≤ j * vectorNorm v := by
    rw [vectorNorm_smul, abs_of_nonneg hB0]
    exact mul_le_mul_of_nonneg_right hB (vectorNorm_nonneg v)
  have hm : vectorNorm (magnetization y) ^ 2 = (n : ℝ) * overlap y := by
    rw [vectorNorm_sq]
    dsimp [vectorSqNorm, overlap]
    field_simp
  have hm_bound : vectorNorm (magnetization y) ^ 2 ≤ n := by nlinarith
  have hs : 0 ≤ 2 * j / (n : ℝ) := by positivity
  have hcs := vector_dot_abs_le (magnetization y) v
  have hrank : vectorNorm (fun i => ((2 * j / n) *
      (∑ k, magnetization y k * v k)) * magnetization y i) ≤ 2 * j * vectorNorm v := by
    rw [vectorNorm_smul, abs_mul, abs_of_nonneg hs]
    calc
      _ ≤ ((2 * j / n) * (vectorNorm (magnetization y) * vectorNorm v)) *
          vectorNorm (magnetization y) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcs hs)
          (vectorNorm_nonneg _)
      _ = (2 * j / n) * vectorNorm (magnetization y) ^ 2 * vectorNorm v := by ring
      _ ≤ (2 * j / n) * n * vectorNorm v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_bound hs)
          (vectorNorm_nonneg _)
      _ = _ := by field_simp
  rw [hessianCore_mulVec]
  calc
    _ ≤ vectorNorm ((fun i => onsager j y * v i) - J.mulVec v) +
        vectorNorm (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) *
          magnetization y i) := vectorNorm_sub_le _ _
    _ ≤ (vectorNorm (fun i => onsager j y * v i) + vectorNorm (J.mulVec v)) +
        vectorNorm (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) *
          magnetization y i) := add_le_add (vectorNorm_sub_le _ _) le_rfl
    _ ≤ (j * vectorNorm v + K * vectorNorm v) + 2 * j * vectorNorm v :=
      add_le_add (add_le_add hfirst (hJ v)) hrank
    _ = _ := by ring

theorem fieldJacobian_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (fieldJacobian j J y).mulVec v = v +
      (hessianCore j J y).mulVec (fun i => spinVariance y i * v i) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, fieldJacobian, add_mul,
    Finset.sum_add_distrib, Pi.add_apply, mul_assoc]
  simp

theorem fieldJacobian_inverse_bound {n : ℕ} (hn : 0 < n) {c j K : ℝ}
    (hc : 0 < c) (hj : 0 ≤ j) (hK : 0 ≤ K)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K * vectorNorm z)
    (hH : ∀ x : Field n, c * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    vectorNorm v ≤ (1 + (K + 3 * j) / c) *
      vectorNorm ((fieldJacobian j J y).mulVec v) := by
  let z := (fieldJacobian j J y).mulVec v
  let w : Field n := fun i => spinVariance y i * v i
  have hw : vectorNorm w ≤ vectorNorm (sqrtVarianceMul y v) := by
    simpa only [sqrtVarianceMul_twice] using sqrtVarianceMul_norm_le y (sqrtVarianceMul y v)
  have hcv : c * vectorNorm w ≤ vectorNorm z :=
    (mul_le_mul_of_nonneg_left hw hc.le).trans (weighted_inverse_bound hc J y v hH)
  have hv : vectorNorm w ≤ vectorNorm z / c := (le_div_iff₀ hc).mpr (by
    simpa only [mul_comm] using hcv)
  have he : v = z - (hessianCore j J y).mulVec w := by
    have hid := fieldJacobian_mulVec j J y v
    change z = v + (hessianCore j J y).mulVec w at hid
    rw [hid, add_sub_cancel_right]
  have hL := hessianCore_norm_le hn hj J y w hJ
  have hD : 0 ≤ K + 3 * j := by positivity
  calc
    vectorNorm v ≤ vectorNorm z + vectorNorm ((hessianCore j J y).mulVec w) := by
      conv_lhs => rw [he]
      exact vectorNorm_sub_le _ _
    _ ≤ vectorNorm z + (K + 3 * j) * vectorNorm w := add_le_add le_rfl hL
    _ ≤ vectorNorm z + (K + 3 * j) * (vectorNorm z / c) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hD)
    _ = (1 + (K + 3 * j) / c) * vectorNorm z := by ring

end SKGap
end
end

end OAI
