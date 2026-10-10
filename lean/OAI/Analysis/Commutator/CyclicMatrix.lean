import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

def matrixAction (X : ι → ι → H →L[ℂ] F) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => F) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j : ι,
      (X i j).comp (PiLp.proj 2 (fun _ : ι => H) j)))

omit [CompleteSpace H] [CompleteSpace F] in
@[simp] lemma matrixAction_apply (X : ι → ι → H →L[ℂ] F)
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) :
    matrixAction X x i=∑ j, X i j (x j) := by
  simp [matrixAction]

def matrixRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    CStarMatrix ι ι A →⋆ₐ[ℂ] (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) where
  toFun X := matrixAction (fun i j => σ (X i j))
  map_zero' := by ext x i; simp
  map_one' := by
    classical
    ext x i
    rw [matrixAction_apply]
    change ∑ j, σ ((1 : CStarMatrix ι ι A) i j) (x j)=x i
    have he (j : ι) : σ ((1 : CStarMatrix ι ι A) i j) (x j)=if i=j then x j else 0 := by
      by_cases h : i=j <;> simp [CStarMatrix.one_apply,h]
    simp_rw [he]
    simp
  map_add' X Y := by
    ext x i
    simp [CStarMatrix.add_apply,Finset.sum_add_distrib]
  map_mul' X Y := by
    ext x i
    simp only [matrixAction_apply,CStarMatrix.mul_apply,map_sum,map_mul,sum_apply,
      mul_apply_eq_comp,map_sum]
    rw [Finset.sum_comm]
  commutes' c := by
    classical
    ext x i
    rw [matrixAction_apply]
    change ∑ j, σ ((algebraMap ℂ (CStarMatrix ι ι A) c) i j) (x j)=c • x i
    have he (j : ι) : σ ((algebraMap ℂ (CStarMatrix ι ι A) c) i j) (x j)=
        if i=j then c • x j else 0 := by
      by_cases h : i=j <;> simp [CStarMatrix.algebraMap_apply,h,Algebra.algebraMap_eq_smul_one]
    simp_rw [he]
    simp
  map_star' X := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [PiLp.inner_apply,matrixAction_apply,CStarMatrix.star_apply,map_star,
      ContinuousLinearMap.star_eq_adjoint,sum_inner,
      ContinuousLinearMap.adjoint_inner_left,inner_sum]
    rw [Finset.sum_comm]

lemma matrixRepresentation_norm_le (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (X : CStarMatrix ι ι A) :
    ‖matrixRepresentation σ X‖ ≤ ‖X‖ :=
  NonUnitalStarAlgHom.norm_apply_le (matrixRepresentation σ) X

def columnNorm (v : ι → A) : ℝ :=
  ‖(WithCStarModule.equiv A (ι → A)).symm (fun i => star (v i))‖

lemma columnNorm_sq (v : ι → A) :
    columnNorm v ^ 2 = ‖∑ i, star (v i)*v i‖ := by
  rw [columnNorm,WithCStarModule.pi_norm_sq]
  simp only [WithCStarModule.equiv_symm_pi_apply,WithCStarModule.inner_def,star_star]

lemma columnNorm_nonneg (v : ι → A) : 0 ≤ columnNorm v := norm_nonneg _

lemma columnNorm_le_one (v : ι → A) (hv : (∑ i,star (v i)*v i)≤1) :
    columnNorm v ≤ 1 := by
  have hp : 0 ≤ ∑ i,star (v i)*v i := Finset.sum_nonneg (fun i _ => star_mul_self_nonneg _)
  have hn : ‖∑ i,star (v i)*v i‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mpr hv
  rw [←columnNorm_sq] at hn
  nlinarith [columnNorm_nonneg v]

lemma columnNorm_matmul_le (X : CStarMatrix ι ι A) (v : ι → A) :
    columnNorm (fun i => ∑ j, X i j*v j) ≤ ‖X‖*columnNorm v := by
  let r := (WithCStarModule.equiv A (ι → A)).symm (fun i => star (v i))
  have heq : (WithCStarModule.equiv A (ι → A)).symm
      (fun i => star (∑ j, X i j*v j)) = CStarMatrix.toCLM (star X) r := by
    ext i
    simp [CStarMatrix.toCLM_apply_eq_sum,CStarMatrix.star_apply,r,star_sum,star_mul]
  dsimp only [columnNorm]
  rw [heq]
  calc ‖CStarMatrix.toCLM (star X) r‖ ≤ ‖CStarMatrix.toCLM (star X)‖*‖r‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖X‖*‖r‖ := by rw [←CStarMatrix.norm_def,norm_star]

end Kadison.CyclicColumns

end

end
end

end OAI
