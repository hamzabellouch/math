import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankOneCovariance (s r : ℝ) (m : ι → ℝ) : Matrix ι ι ℝ :=
  s • (1 : Matrix ι ι ℝ)+r • vecMulVec m m

def rankOneCovarianceInverse (s r : ℝ) (m : ι → ℝ) : Matrix ι ι ℝ :=
  s⁻¹ • (1 : Matrix ι ι ℝ)-(r/(s*(s+r*(m⬝ᵥm)))) • vecMulVec m m

lemma rankOneCovarianceInverse_mul (s r : ℝ) (m : ι → ℝ)
    (hs : s ≠ 0) (hS : s+r*(m⬝ᵥm) ≠ 0) :
    rankOneCovarianceInverse s r m * rankOneCovariance s r m=1 := by
  simp only [rankOneCovarianceInverse,rankOneCovariance,Matrix.sub_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
    Matrix.vecMulVec_mul_vecMulVec]
  ext i k
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.vecMulVec_apply,Pi.smul_apply]
  field_simp [hs,hS]
  ring

lemma rankOneCovarianceInverse_mulVec (s r : ℝ) (m y : ι → ℝ) (i : ι) :
    (rankOneCovarianceInverse s r m*ᵥy) i =
      s⁻¹*y i-r/(s*(s+r*(m⬝ᵥm)))*(m⬝ᵥy)*m i := by
  simp only [rankOneCovarianceInverse,Matrix.sub_mulVec,Matrix.smul_mulVec,
    Matrix.one_mulVec,Matrix.vecMulVec_mulVec,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,op_smul_eq_smul]
  ring

lemma rankOneCovariance_posDef {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) (m : ι → ℝ) :
    (rankOneCovariance s r m).PosDef := by
  apply (Matrix.PosDef.smul (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef) hs).add_posSemidef
  have hh : (vecMulVec m m).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star m
  exact hh.smul hr

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rankOneCovariance_det {s : ℝ} (hs : s ≠ 0) (r : ℝ) (m : ι → ℝ) :
    (rankOneCovariance s r m).det=s^(Fintype.card ι)*(1+(r/s)*(m⬝ᵥm)) := by
  have he : rankOneCovariance s r m=s • (1+vecMulVec ((r/s) • m) m) := by
    ext i k
    simp only [rankOneCovariance,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.vecMulVec_apply,Pi.smul_apply]
    field_simp
  rw [he,Matrix.det_smul,Matrix.vecMulVec_eq Unit,Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct_smul,smul_eq_mul]

lemma rankOneCovarianceInverse_quad (s r : ℝ) (m x : ι → ℝ) :
    x⬝ᵥ(rankOneCovarianceInverse s r m*ᵥx)=
      s⁻¹*(x⬝ᵥx)-r/(s*(s+r*(m⬝ᵥm)))*(m⬝ᵥx)^2 := by
  simp only [dotProduct,rankOneCovarianceInverse_mulVec,mul_sub,Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · have hh : (∑ i,x i*(r/(s*(s+r*∑ j,m j*m j))*(∑ j,m j*x j)*m i))=
      (r/(s*(s+r*∑ j,m j*m j))*(∑ j,m j*x j))*(∑ i,m i*x i) := by
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hh]
    ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankOneTransform (a b : ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  a • (1 : Matrix ι ι ℝ)+(b-a) • vecMulVec u u

omit [Fintype ι] in
lemma rankOneTransform_transpose (a b : ℝ) (u : ι → ℝ) :
    (rankOneTransform a b u)ᵀ=rankOneTransform a b u := by
  ext i k
  simp [rankOneTransform,Matrix.one_apply,Matrix.vecMulVec_apply,eq_comm,mul_comm]

lemma rankOneTransform_mul {u : ι → ℝ} (hu : u⬝ᵥu=1) (a b c d : ℝ) :
    rankOneTransform a b u *rankOneTransform c d u =rankOneTransform (a*c) (b*d) u := by
  simp only [rankOneTransform,Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,Matrix.vecMulVec_mul_vecMulVec,hu]
  ext i k
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,Pi.smul_apply]
  ring

lemma rankOneTransform_det {a : ℝ} (ha : a ≠ 0) (b : ℝ) {u : ι → ℝ} (hu : u⬝ᵥu=1) :
    (rankOneTransform a b u).det=a^(Fintype.card ι)*(b/a) := by
  have he : rankOneTransform a b u=rankOneCovariance a (b-a) u := rfl
  rw [he,rankOneCovariance_det ha,hu,mul_one]
  congr 1
  field_simp
  ring

lemma rankOneTransform_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) :
    (rankOneTransform a b u)⁻¹=rankOneTransform a⁻¹ b⁻¹ u := by
  apply Matrix.inv_eq_left_inv
  rw [rankOneTransform_mul hu,inv_mul_cancel₀ ha,inv_mul_cancel₀ hb]
  simp [rankOneTransform]

lemma rankOneTransform_mulVec (a b : ℝ) (u x : ι → ℝ) :
    rankOneTransform a b u*ᵥx=a • x+((b-a)*(u⬝ᵥx)) • u := by
  ext i
  simp only [rankOneTransform,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec,Pi.add_apply,Pi.smul_apply,smul_eq_mul,op_smul_eq_smul]
  ring

lemma rankOneTransform_norm_sq {u : ι → ℝ} (hu : u⬝ᵥu=1) (a b : ℝ) (x : ι → ℝ) :
    (rankOneTransform a b u*ᵥx)⬝ᵥ(rankOneTransform a b u*ᵥx)=
      a^2*(x⬝ᵥx)+(b^2-a^2)*(u⬝ᵥx)^2 := by
  rw [rankOneTransform_mulVec]
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,hu]
  rw [dotProduct_comm x u]
  ring

end SKGap
end
end

end OAI
