import OAI.Analysis.FreeEntropy.MatrixChartInverse

namespace OAI

noncomputable section
open scoped ComplexConjugate Matrix.Norms.L2Operator
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def hsVector (A : Matrix (Fin d) (Fin d) ℂ) : EuclideanSpace ℂ (Fin d×Fin d) :=
    WithLp.toLp 2 (fun q => A q.1 q.2)
 def hsNorm (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := ‖hsVector A‖
 theorem hsNorm_sq (A : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm A^2=∑j,∑k,Complex.normSq (A j k) := by
  rw [hsNorm,EuclideanSpace.norm_sq_eq]
  simp [hsVector,Fintype.sum_prod_type,Complex.normSq_eq_norm_sq]
 theorem hsNorm_nonneg (A : Matrix (Fin d) (Fin d) ℂ) : 0≤hsNorm A := norm_nonneg _
 theorem hsNorm_add (A B : Matrix (Fin d) (Fin d) ℂ) : hsNorm (A+B) ≤ hsNorm A+hsNorm B := by
  have he : hsVector (A+B)=hsVector A+hsVector B := by ext q; rfl
  simpa only [hsNorm,he] using norm_add_le (hsVector A) (hsVector B)
 theorem hsNorm_sub (A B : Matrix (Fin d) (Fin d) ℂ) : hsNorm (A-B) ≤ hsNorm A+hsNorm B := by
  have he : hsVector (A-B)=hsVector A-hsVector B := by ext q; rfl
  simpa only [hsNorm,he] using norm_sub_le (hsVector A) (hsVector B)
 theorem hsNorm_star (A : Matrix (Fin d) (Fin d) ℂ) : hsNorm A.conjTranspose=hsNorm A := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  simp only [hsNorm_sq,Matrix.conjTranspose_apply,Complex.star_def,Complex.normSq_conj]
  exact sum_comm
 theorem hsNorm_mul_left (A B : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm (A*B) ≤ matrixOpNorm A*hsNorm B := by
  have hcol k : (∑j,Complex.normSq ((A*B) j k)) ≤ matrixOpNorm A^2*(∑j,Complex.normSq (B j k)) := by
    let x : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (fun j => B j k)
    have hh := (matrixOperator A).le_opNorm x
    have hn : ‖matrixOperator A x‖^2 ≤ (matrixOpNorm A*‖x‖)^2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa [matrixOperator,Matrix.toLpLin_apply,EuclideanSpace.norm_sq_eq,Matrix.mul_apply,
      Matrix.mulVec, dotProduct, x,Complex.normSq_eq_norm_sq,mul_pow,matrixOpNorm] using hn
  have hh := sum_le_sum (fun k (_ : k∈(univ:Finset (Fin d))) => hcol k)
  rw [sum_comm] at hh
  simp only [← mul_sum] at hh
  rw [sum_comm (f := fun i j : Fin d => Complex.normSq (B j i)),← hsNorm_sq,← hsNorm_sq] at hh
  have hb := hsNorm_nonneg B
  have hab := hsNorm_nonneg (A*B)
  have ha := matrixOpNorm_nonneg A
  apply (sq_le_sq₀ hab (mul_nonneg ha hb)).mp
  simpa only [mul_pow] using hh
 theorem hsNorm_mul_right (A B : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm (A*B) ≤ hsNorm A*matrixOpNorm B := by
  rw [← hsNorm_star (A*B),Matrix.conjTranspose_mul]
  have hh := hsNorm_mul_left B.conjTranspose A.conjTranspose
  rw [hsNorm_star] at hh
  have he : matrixOpNorm B.conjTranspose=matrixOpNorm B := Matrix.l2_opNorm_conjTranspose B
  rw [he,mul_comm] at hh
  exact hh
 theorem hsNorm_unitary_conjugate (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm (star (U:Matrix (Fin d) (Fin d) ℂ)*A*(U:Matrix (Fin d) (Fin d) ℂ))=hsNorm A := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  rw [hsNorm_sq,hsNorm_sq,← trace_conjTranspose_mul_re,← trace_conjTranspose_mul_re]
  congr 1
  simp only [← Matrix.star_eq_conjTranspose,star_mul,star_star]
  have h1 : (U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)=1 := Unitary.coe_mul_star_self U
  have h2 : star (U:Matrix (Fin d) (Fin d) ℂ)*(U:Matrix (Fin d) (Fin d) ℂ)=1 := Unitary.coe_star_mul_self U
  calc
    _ = Matrix.trace (star (U:Matrix (Fin d) (Fin d) ℂ)*(star A*A)*(U:Matrix (Fin d) (Fin d) ℂ)) := by
      congr 1
      calc
        _ = star (U:Matrix (Fin d) (Fin d) ℂ)*star A*((U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ))*A*(U:Matrix (Fin d) (Fin d) ℂ) := by noncomm_ring
        _ = _ := by rw [h1]; noncomm_ring
    _ = _ := by rw [Matrix.trace_mul_cycle, h1,one_mul]
 theorem hermitianChart_injective : Function.Injective (hermitianChart n d) := by
  intro a b hab
  have he : hermitianChart n d (a-b)=0 := by rw [map_sub,hab,sub_self]
  have hz := hermitianChart_normSq (a-b)
  have hh : ∀i,hermitianMatrix (a-b) i=0 := congrFun he
  simp only [hh,Matrix.zero_apply,map_zero,sum_const_zero] at hz
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (a-b)]))
 theorem matrixCoordinates_hermitianMatrix (a : MatrixCoordinates n d) :
    matrixCoordinatesOfHermitian (hermitianMatrix a)=a := by
  apply hermitianChart_injective
  funext i
  exact hermitianMatrix_coordinatesOfHermitian _ (hermitianMatrix_isHermitian a) i
 def rotateCoordinates (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (a : MatrixCoordinates n d) : MatrixCoordinates n d :=
    matrixCoordinatesOfHermitian (fun i => star (U:Matrix (Fin d) (Fin d) ℂ)*hermitianMatrix a i*U)
 theorem conjugate_hermitian (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) : (star (U:Matrix (Fin d) (Fin d) ℂ)*A*U).IsHermitian := by
  change star _ = _
  simp only [star_mul,star_star]
  rw [show star A=A from hA]
  simp only [mul_assoc]
 theorem hermitianMatrix_rotate (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (a : MatrixCoordinates n d) (i : Fin n) :
    hermitianMatrix (rotateCoordinates U a) i=star (U:Matrix (Fin d) (Fin d) ℂ)*hermitianMatrix a i*U :=
  hermitianMatrix_coordinatesOfHermitian _ (fun i => conjugate_hermitian U _ (hermitianMatrix_isHermitian a i)) i
 theorem rotateCoordinates_norm (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (a : MatrixCoordinates n d) :
    ‖rotateCoordinates U a‖=‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← hermitianChart_normSq,← hermitianChart_normSq]
  simp_rw [hermitianMatrix_rotate,← hsNorm_sq]
  apply sum_congr rfl
  intro i _
  rw [hsNorm_unitary_conjugate]
 def rotateLinearIsometryEquiv (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    MatrixCoordinates n d ≃ₗᵢ[ℝ] MatrixCoordinates n d where
  toFun := rotateCoordinates U
  invFun := rotateCoordinates (star U)
  left_inv a := by
    apply hermitianChart_injective
    funext i
    simp only [hermitianChart,LinearMap.coe_mk,AddHom.coe_mk,hermitianMatrix_rotate,Unitary.coe_star,star_star]
    have h : (U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)=1 := Unitary.coe_mul_star_self U
    calc
      _ = ((U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ))*hermitianMatrix a i*((U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)) := by noncomm_ring
      _ = _ := by rw [h,one_mul,mul_one]
  right_inv a := by
    apply hermitianChart_injective
    funext i
    simp only [hermitianChart,LinearMap.coe_mk,AddHom.coe_mk,hermitianMatrix_rotate,Unitary.coe_star,star_star]
    have h : star (U:Matrix (Fin d) (Fin d) ℂ)*(U:Matrix (Fin d) (Fin d) ℂ)=1 := Unitary.coe_star_mul_self U
    calc
      _ = (star (U:Matrix (Fin d) (Fin d) ℂ)*(U:Matrix (Fin d) (Fin d) ℂ))*hermitianMatrix a i*(star (U:Matrix (Fin d) (Fin d) ℂ)*(U:Matrix (Fin d) (Fin d) ℂ)) := by noncomm_ring
      _ = _ := by rw [h,one_mul,mul_one]
  map_add' a b := by
    apply hermitianChart_injective
    funext i
    simp [hermitianChart,hermitianMatrix_rotate,hermitianMatrix_add,mul_add,add_mul]
  map_smul' r a := by
    apply hermitianChart_injective
    funext i
    simp [hermitianChart,hermitianMatrix_rotate,hermitianMatrix_smul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
  norm_map' := rotateCoordinates_norm U
end FiniteEntropySeparation

end

end OAI
