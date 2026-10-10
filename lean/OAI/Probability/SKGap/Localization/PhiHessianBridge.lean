import Mathlib
import OAI.Probability.SKGap.Stability.ImplicitPerturb

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma rank_toEuclideanCLM (m : Fin n→ℝ) :
    toEuclideanCLM (𝕜:=ℝ) (vecMulVec m m)=rank (WithLp.toLp 2 m) (WithLp.toLp 2 m) := by
  ext v i
  change ((vecMulVec m m).mulVec v.ofLp) i=(inner ℝ (WithLp.toLp 2 m) v)*m i
  simp only [mulVec, dotProduct, vecMulVec]
  change (∑k,m i*m k*v k)=(∑k,v k*m k)*m i
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

lemma fieldHessian_matrix (j : ℝ) (J : Interaction n) (z A : Fin n→ℝ) :
    SKGap.fieldHessian j J z A=
      1+(SKGap.onsager j z) • ((diagonal (fun i=>Real.sqrt (A i)))*(diagonal (fun i=>Real.sqrt (A i))))-
        diagonal (fun i=>Real.sqrt (A i))*J*diagonal (fun i=>Real.sqrt (A i))-
        (2*j/(n:ℝ)) • (diagonal (fun i=>Real.sqrt (A i))*
          vecMulVec (SKGap.magnetization z) (SKGap.magnetization z)*diagonal (fun i=>Real.sqrt (A i))) := by
  ext i k
  simp only [SKGap.fieldHessian,SKGap.hessianCore,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.diagonal_apply,vecMulVec,Matrix.of_apply]
  by_cases h:i=k
  · subst k; simp only [ite_true];ring
  · simp only [h,ite_false];ring

lemma onsager_scalarVariance (hn : 0<n) (j : ℝ) (z : Fin n→ℝ) :
    SKGap.onsager j z=j*((∑i,scalarVariance (z i))/(n:ℝ)) := by
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [SKGap.onsager,SKGap.overlap,SKGap.magnetization,scalarVariance]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp

lemma literal_stableMatrix_eq_hessian (hn : 0<n) (j : ℝ) (J : Interaction n)
    (z r : Fin n→ℝ) (a : ℝ) :
    stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
      (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (fun i=>Real.tanh (z i)))=
      toEuclideanCLM (𝕜:=ℝ) (SKGap.fieldHessian j J z (fun i=>phi (z i) (r i) a)) := by
  rw [fieldHessian_matrix]
  simp only [map_sub,map_add,map_one,map_smul,map_mul,rank_toEuclideanCLM]
  rw [onsager_scalarVariance hn]
  simp only [stableMatrix,phiSqrt,div_eq_mul_inv]
  rfl

lemma literal_stableMatrix_quadratic (hn : 0<n) (j : ℝ) (J : Interaction n)
    (z r : Fin n→ℝ) (a : ℝ) (v : Euclid n) :
    inner ℝ v (stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
      (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (fun i=>Real.tanh (z i))) v)=
      SKGap.quadraticForm (SKGap.fieldHessian j J z (fun i=>phi (z i) (r i) a)) v.ofLp := by
  rw [literal_stableMatrix_eq_hessian hn,Matrix.inner_toEuclideanCLM]
  simp only [dotProduct,mulVec,SKGap.quadraticForm,Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext k
  ring

end SKGapCutoff.Recipe

end
end

end OAI
