import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.DistanceSquare
import OAI.Geometry.SmoothYau.Smoothness.FderivCofactorApply

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma hasDerivAt_det_exp_smul (K : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • K)).det)
      ((NormedSpace.exp (t • K)).det * K.trace) t := by
  have hu : IsUnit (NormedSpace.exp (t • K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (NormedSpace.isUnit_exp (t • K))
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) K t
  have hd := (differentiable_det (NormedSpace.exp (t • K))).hasFDerivAt.comp_hasDerivAt t he
  erw [fderiv_det_apply _ _ hu,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one] at hd
  exact hd

theorem matrix_det_exp (K : Matrix ι ι ℝ) :
    (NormedSpace.exp K).det = Real.exp K.trace := by
  let f : ℝ → ℝ := fun t => (NormedSpace.exp (t • K)).det * Real.exp (-t * K.trace)
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have hh := (hasDerivAt_det_exp_smul K t).mul
      (((hasDerivAt_id t).neg.mul_const K.trace).exp)
    convert hh using 1 <;> first | rfl | ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
    (fun t => (hf t).deriv) 1 0
  have hfe : (NormedSpace.exp K).det * Real.exp (-K.trace) = 1 := by
    simpa only [f,one_smul,neg_mul,one_mul,zero_smul,NormedSpace.exp_zero,Matrix.det_one,
      neg_zero,zero_mul,Real.exp_zero,mul_one] using hc
  calc (NormedSpace.exp K).det =
      (NormedSpace.exp K).det * (Real.exp (-K.trace) * Real.exp K.trace) := by
        rw [← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
    _ = Real.exp K.trace := by rw [← mul_assoc,hfe,one_mul]

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open scoped Matrix.Norms.Operator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def clmMatrixAlgHom (b : Module.Basis ι ℝ E) : (E →L[ℝ] E) →ₐ[ℝ] Matrix ι ι ℝ where
  toFun K := LinearMap.toMatrix b b K.toLinearMap
  map_one' := by simp
  map_mul' A B := by simp [LinearMap.toMatrix_mul]
  map_zero' := by simp
  map_add' A B := by simp
  commutes' r := by
    change LinearMap.toMatrix b b (r • LinearMap.id) = _
    simp [Algebra.algebraMap_eq_smul_one]

lemma clmMatrix_exp (b : Module.Basis ι ℝ E) (K : E →L[ℝ] E) :
    LinearMap.toMatrix b b (NormedSpace.exp K).toLinearMap =
      NormedSpace.exp (LinearMap.toMatrix b b K.toLinearMap) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  exact NormedSpace.map_exp (clmMatrixAlgHom b)
    (clmMatrixAlgHom b).toLinearMap.continuous_of_finiteDimensional K

lemma clm_det_exp (b : Module.Basis ι ℝ E) (K : E →L[ℝ] E) :
    LinearMap.det (NormedSpace.exp K).toLinearMap =
      Real.exp (LinearMap.trace ℝ E K.toLinearMap) := by
  rw [← LinearMap.det_toMatrix b,clmMatrix_exp b K,matrix_det_exp,
    LinearMap.trace_eq_matrix_trace ℝ b]

def matrixOfForm (b : Module.Basis ι ℝ E) (G : E →L[ℝ] E →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j => G (b i) (b j)

omit [FiniteDimensional ℝ E] in
lemma matrixOfForm_pullback (b : Module.Basis ι ℝ E) (G : E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E) :
    matrixOfForm b ((D.precomp ℝ).comp (G.comp D)) =
      (clmMatrixAlgHom b D).transpose * matrixOfForm b G * clmMatrixAlgHom b D := by
  ext i j
  change G (D (b i)) (D (b j)) =
    ((LinearMap.toMatrix b b D.toLinearMap).transpose * matrixOfForm b G *
      LinearMap.toMatrix b b D.toLinearMap) i j
  conv_lhs => arg 1; rw [← b.sum_repr (D (b i))]
  conv_lhs => arg 2; rw [← b.sum_repr (D (b j))]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,matrixOfForm,
    LinearMap.toMatrix_apply,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change (b.repr (D (b j))) k * ((b.repr (D (b i))) l * G (b l) (b k)) =
    (b.repr (D (b i))) l * G (b l) (b k) * (b.repr (D (b j))) k
  ring

theorem tracefree_exp_preserves_gram_det (b : Module.Basis ι ℝ E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (htr : LinearMap.trace ℝ E K.toLinearMap = 0) :
    (matrixOfForm b (((NormedSpace.exp K).precomp ℝ).comp
      (G.comp (NormedSpace.exp K)))).det = (matrixOfForm b G).det := by
  rw [matrixOfForm_pullback,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  have hd : (clmMatrixAlgHom b (NormedSpace.exp K)).det = 1 := by
    change (LinearMap.toMatrix b b (NormedSpace.exp K).toLinearMap).det = 1
    rw [LinearMap.det_toMatrix,clm_det_exp b K,htr,Real.exp_zero]
  rw [hd,one_mul,mul_one]


end YauCounterexamples
end

end OAI
