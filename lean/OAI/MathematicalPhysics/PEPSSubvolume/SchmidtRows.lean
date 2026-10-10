import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.ModularScalar

namespace OAI

/-! Normalized Schmidt rows and singular-safe matrix distortion. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open PolynomialPEPS.PinnedEntropy

open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
namespace PolynomialPEPS.Subvolume.NormalizedRows
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def root (p : ι → ℝ) : Matrix ι ι ℂ := diagonal (fun i => (Real.sqrt (p i) : ℂ))
def inverseRoot (p : ι → ℝ) : Matrix ι ι ℂ := diagonal (fun i => ((Real.sqrt (p i) : ℂ))⁻¹)
def kernel (p : ι → ℝ) : Matrix ι ι ℂ := diagonal (fun i => if p i=0 then 1 else 0)
def rows (W : Matrix ι κ ℂ) (p : ι → ℝ) : Matrix ι κ ℂ := inverseRoot p * W

omit [Fintype ι] in
lemma kernel_hermitian (p : ι → ℝ) : (kernel p).conjTranspose = kernel p := by
  simp [kernel]

omit [Fintype ι] in
lemma inverseRoot_hermitian (p : ι → ℝ) : (inverseRoot p).conjTranspose = inverseRoot p := by
  simp [inverseRoot]

lemma kernel_mul_weights (p : ι → ℝ) : kernel p * diagonal (fun i => (p i : ℂ)) = 0 := by
  rw [kernel,diagonal_mul_diagonal]
  ext i j
  by_cases h : p i=0 <;> simp [diagonal_apply,h]

omit [DecidableEq κ] in
lemma kernel_mul_zero (W : Matrix ι κ ℂ) (p : ι → ℝ)
    (hW : W*W.conjTranspose = diagonal (fun i => (p i : ℂ))) : kernel p * W = 0 := by
  apply Matrix.self_mul_conjTranspose_eq_zero.mp
  rw [conjTranspose_mul,kernel_hermitian]
  calc
    _ = kernel p * (W*W.conjTranspose) * kernel p := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hW,kernel_mul_weights,zero_mul]

lemma root_inverse (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    root p * inverseRoot p + kernel p = 1 := by
  rw [root,inverseRoot,kernel,diagonal_mul_diagonal,diagonal_add,← diagonal_one]
  congr 1
  ext i
  by_cases h : p i=0
  · simp [h]
  · have hs : (Real.sqrt (p i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hp i) (Ne.symm h)))
    simp [h,hs]

omit [DecidableEq κ] in
lemma reconstruction (W : Matrix ι κ ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hW : W*W.conjTranspose = diagonal (fun i => (p i : ℂ))) : root p * rows W p = W := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M*W) (root_inverse p hp)
  rw [Matrix.add_mul,kernel_mul_zero W p hW,add_zero,Matrix.one_mul] at h
  simpa only [rows,Matrix.mul_assoc] using h

omit [DecidableEq κ] in
lemma rows_gram (W : Matrix ι κ ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hW : W*W.conjTranspose = diagonal (fun i => (p i : ℂ))) :
    rows W p * (rows W p).conjTranspose = 1-kernel p := by
  unfold rows
  rw [conjTranspose_mul,inverseRoot_hermitian]
  calc
    _ = inverseRoot p * (W*W.conjTranspose) * inverseRoot p := by simp only [Matrix.mul_assoc]
    _ = 1-kernel p := by
      rw [hW,inverseRoot,kernel,diagonal_mul_diagonal,diagonal_mul_diagonal,
        ← diagonal_one,diagonal_sub]
      congr 1
      ext i
      by_cases h : p i=0
      · simp [h]
      · have hs : Real.sqrt (p i) ≠ 0 :=
          Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hp i) (Ne.symm h))
        have hsC := Complex.ofReal_ne_zero.mpr hs
        have hsq : (Real.sqrt (p i) : ℂ)^2 = (p i : ℂ) := by
          norm_cast
          exact Real.sq_sqrt (hp i)
        simp only [h,ite_false,sub_zero]
        rw [← hsq]
        field_simp

lemma rows_norm_le (W : Matrix ι κ ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hW : W*W.conjTranspose = diagonal (fun i => (p i : ℂ))) : ‖rows W p‖ ≤ 1 := by
  have hnorm : ‖(1 : Matrix ι ι ℂ)-kernel p‖ ≤ 1 := by
    rw [kernel,← diagonal_one,diagonal_sub,l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro i
    by_cases h : p i=0 <;> simp [h]
  have hc := Matrix.l2_opNorm_conjTranspose_mul_self (rows W p).conjTranspose
  rw [conjTranspose_conjTranspose,rows_gram W p hp hW,l2_opNorm_conjTranspose] at hc
  rw [hc] at hnorm
  nlinarith [norm_nonneg (rows W p)]

theorem effective_norm_le (W : Matrix ι κ ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hW : W*W.conjTranspose = diagonal (fun i => (p i : ℂ))) (B : Matrix κ κ ℂ) :
    ‖rows W p * B * (rows W p).conjTranspose‖ ≤ ‖B‖ := by
  have hK := rows_norm_le W p hp hW
  calc
    _ ≤ (‖rows W p‖*‖B‖)*‖(rows W p).conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
        (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖B‖)*1 := by rw [l2_opNorm_conjTranspose]; gcongr
    _ = _ := by ring

end PolynomialPEPS.Subvolume.NormalizedRows

namespace PolynomialPEPS.Subvolume.ModularMatrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.NormalizedRows PolynomialPEPS.Subvolume.ModularScalar
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def weightPower (p : ι → ℝ) (a : ℝ) : Matrix ι ι ℂ :=
  diagonal (fun i => ((p i)^a : ℝ))

def weightInverse (p : ι → ℝ) (a : ℝ) : Matrix ι ι ℂ :=
  diagonal (fun i => (((p i)^a : ℝ) : ℂ)⁻¹)

def distortion (A : Matrix ι ι ℂ) (p : ι → ℝ) (a : ℝ) : Matrix ι ι ℂ :=
  (1/2 : ℂ) • (weightPower p a * A * weightInverse p a +
    weightInverse p a * A * weightPower p a) - A

def bilinearExpectation (W : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : ℂ :=
  ∑ i, ∑ j, A i j * (W*B*W.conjTranspose) i j

omit [DecidableEq κ] in
lemma covariance (W : Matrix ι κ ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hW : W*W.conjTranspose = diagonal (fun i => (p i : ℂ))) (B : Matrix κ κ ℂ) :
    W*B*W.conjTranspose = root p * (rows W p * B * (rows W p).conjTranspose) * root p := by
  have hr : (root p).conjTranspose = root p := by simp [root]
  calc
    _ = (root p * rows W p)*B*(root p * rows W p).conjTranspose := by rw [reconstruction W p hp hW]
    _ = _ := by rw [conjTranspose_mul,hr]; simp only [Matrix.mul_assoc]

omit [DecidableEq κ] in
lemma entry_identity (W : Matrix ι κ ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hW : W*W.conjTranspose = diagonal (fun i => (p i : ℂ)))
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (a : ℝ) (i j : ι) :
    distortion A p a i j * (W*B*W.conjTranspose) i j =
      (modularCoefficient (p i) (p j) a : ℂ) * A i j *
        (rows W p * B * (rows W p).conjTranspose) i j := by
  rw [covariance W p hp hW B]
  simp only [distortion,weightPower,weightInverse,root,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,smul_eq_mul]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (modularCoefficient_formula (p i) (p j) a (hp i) (hp j))
  push_cast at h
  rw [← h]
  ring

theorem product_error_le (W : Matrix ι κ ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hW : W*W.conjTranspose = diagonal (fun i => (p i : ℂ)))
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (a : ℝ) (ha : |a| ≤ 1/4) :
    ‖bilinearExpectation W (distortion A p a) B‖ ≤
      32*a^2*(∑ i, p i)*(‖A‖*‖B‖) := by
  let E := rows W p * B * (rows W p).conjTranspose
  have hsum : bilinearExpectation W (distortion A p a) B =
      ∑ i, ∑ j, (modularCoefficient (p i) (p j) a : ℂ)*A i j*E i j := by
    unfold bilinearExpectation
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact entry_identity W p hp hW A B a i j
  rw [hsum]
  have hd : ∀ i j, ‖(modularCoefficient (p i) (p j) a : ℂ)‖ ≤ 16*a^2*max (p i) (p j) := by
    intro i j
    simpa only [Complex.norm_real,Real.norm_eq_abs] using modularCoefficient_bound (p i) (p j) a (hp i) (hp j) ha
  calc
    _ ≤ 2*(16*a^2)*(∑ i, p i)*(‖A‖*‖E‖) :=
      MatrixRows.coefficient_sum A E p hp _ _ (by positivity) hd
    _ ≤ 2*(16*a^2)*(∑ i, p i)*(‖A‖*‖B‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (effective_norm_le W p hp hW B) (norm_nonneg A))
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hp i))
    _ = _ := by ring

end PolynomialPEPS.Subvolume.ModularMatrix

namespace PolynomialPEPS.Subvolume.ModularMatrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.NormalizedRows PolynomialPEPS.Subvolume.ModularScalar
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma gram_real_smul (W : Matrix ι κ ℂ) (c : ℝ) :
    ((c:ℂ) • W) * ((c:ℂ) • W).conjTranspose = (c^2:ℂ) • (W*W.conjTranspose) := by
  rw [conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  simp [sq]

omit [DecidableEq ι] [DecidableEq κ] in
lemma bilinear_real_smul (W : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (c : ℝ) :
    bilinearExpectation ((c:ℂ) • W) A B = (c^2:ℂ)*bilinearExpectation W A B := by
  simp only [bilinearExpectation,conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.smul_apply,smul_eq_mul,Complex.star_def,
    Complex.conj_ofReal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem scaled_product_error_le (W : Matrix ι κ ℂ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (c : ℝ) (hc : 0 ≤ c)
    (hW : W*W.conjTranspose = (c^2:ℂ) • diagonal (fun i => (p i : ℂ)))
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (a : ℝ) (ha : |a| ≤ 1/4) :
    ‖bilinearExpectation W (distortion A p a) B‖ ≤
      32*a^2*c^2*(∑ i, p i)*(‖A‖*‖B‖) := by
  by_cases hc0 : c=0
  · rw [hc0,Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_smul] at hW
    have hz := Matrix.self_mul_conjTranspose_eq_zero.mp hW
    simp [hz,bilinearExpectation,hc0]
  let W' : Matrix ι κ ℂ := ((c⁻¹:ℝ):ℂ) • W
  have hW' : W'*W'.conjTranspose = diagonal (fun i => (p i : ℂ)) := by
    dsimp only [W']
    rw [gram_real_smul,hW,smul_smul]
    have hfac : ((c⁻¹:ℝ):ℂ)^2*(c:ℂ)^2=1 := by
      push_cast
      field_simp
    rw [hfac,one_smul]
  have hrec : W=(c:ℂ) • W' := by
    dsimp only [W']
    rw [smul_smul]
    simp [hc0]
  rw [hrec,bilinear_real_smul,norm_mul]
  have hnorm : ‖(c^2:ℂ)‖ = c^2 := by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  rw [hnorm]
  calc
    _ ≤ c^2*(32*a^2*(∑ i, p i)*(‖A‖*‖B‖)) :=
      mul_le_mul_of_nonneg_left (product_error_le W' p hp hW' A B a ha) (sq_nonneg c)
    _ = _ := by ring

end PolynomialPEPS.Subvolume.ModularMatrix

end

end OAI
