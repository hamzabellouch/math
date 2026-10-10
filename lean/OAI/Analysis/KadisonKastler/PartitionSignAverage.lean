import OAI.Analysis.KadisonKastler.FiniteProjectionPartition
import OAI.Analysis.KadisonKastler.FiniteSignFourthMoment
import Mathlib.Algebra.Order.BigOperators.Expect

namespace OAI

/-! # The sign average of a finite projection partition -/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance partitionOperatorNNRat : Module ℚ≥0 (H →L[ℂ] H) :=
  Module.compHom (H →L[ℂ] H) (algebraMap ℚ≥0 ℂ)

def partitionSignOperator (P : ι → AlgebraProjection M) (ε : ι → Bool) : Algebra M :=
  ∑ i, finiteSign ε i • (P i).val

omit [DecidableEq ι] in
theorem partitionSignOperator_val (P : ι → AlgebraProjection M) (ε : ι → Bool) :
    (partitionSignOperator P ε).val=∑ i, finiteSign ε i • (P i).val.val := by
  change M.toStarSubalgebra.subtype (∑ i, finiteSign ε i • (P i).val)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((finiteSign ε i : ℂ) • (P i).val).val=(finiteSign ε i : ℂ) • (P i).val.val
  rfl

omit [DecidableEq ι] in
theorem partitionSignOperator_star (P : ι → AlgebraProjection M) (ε : ι → Bool) :
    star (partitionSignOperator P ε)=partitionSignOperator P ε := by
  simp only [partitionSignOperator,star_sum,star_smul,star_trivial]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun a : Algebra M => finiteSign ε i • a)
    (P i).property.isSelfAdjoint.star_eq

omit [DecidableEq ι] in
theorem partitionSignOperator_sq (P : ι → AlgebraProjection M)
    (hP : Pairwise (fun i j => (P i).val*(P j).val=0))
    (hs : (∑ i, (P i).val)=1) (ε : ι → Bool) :
    partitionSignOperator P ε*partitionSignOperator P ε=1 := by
  classical
  rw [partitionSignOperator,Finset.sum_mul]
  simp only [Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
  have hd (i : ι) : ∑ j, (finiteSign ε j*finiteSign ε i) • ((P i).val*(P j).val)=(P i).val := by
    rw [Finset.sum_eq_single i]
    · rw [← pow_two,finiteSign_sq,one_smul,(P i).property.isIdempotentElem.eq]
    · intro j _ hji
      rw [hP (Ne.symm hji),smul_zero]
    · simp
  simpa only [hd] using hs

omit [DecidableEq ι] in
theorem partitionSignOperator_unitary (P : ι → AlgebraProjection M)
    (hP : Pairwise (fun i j => (P i).val*(P j).val=0))
    (hs : (∑ i, (P i).val)=1) (ε : ι → Bool) :
    partitionSignOperator P ε ∈ unitary (Algebra M) := by
  constructor <;> rw [partitionSignOperator_star,partitionSignOperator_sq P hP hs]

omit [CompleteSpace H] in
theorem conjugationOperator_real_smul (J : H ≃ₗᵢ⋆[ℂ] H) (t : ℝ) (a : H →L[ℂ] H) :
    conjugationOperator J (t • a)=t • conjugationOperator J a := by
  rw [← Complex.coe_smul,conjugationOperator_smul,Complex.star_def,Complex.conj_ofReal,
    Complex.coe_smul]

omit [CompleteSpace H] [DecidableEq ι] in
theorem conjugationOperator_finite_sum (J : H ≃ₗᵢ⋆[ℂ] H) (a : ι → H →L[ℂ] H) :
    conjugationOperator J (∑ i, a i)=∑ i, conjugationOperator J (a i) := by
  ext x
  simp only [conjugationOperator_apply,sum_apply,map_sum]

omit [DecidableEq ι] in
theorem partitionSignOperator_quadratic (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → AlgebraProjection M) (ε : ι → Bool) :
    modularQuadratic J (partitionSignOperator P ε)=
      ∑ i, ∑ j, (finiteSign ε i*finiteSign ε j) •
        ((P i).val.val*conjugationOperator J (P j).val.val) := by
  classical
  rw [modularQuadratic,partitionSignOperator_val,conjugationOperator_finite_sum]
  simp_rw [conjugationOperator_real_smul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [mul_comm (finiteSign ε j) (finiteSign ε i)]

theorem expect_partitionSignOperator_quadratic (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → AlgebraProjection M) :
    (𝔼 ε : ι → Bool, modularQuadratic J (partitionSignOperator P ε))=
      ∑ i, modularQuadratic J (P i).val := by
  simp only [partitionSignOperator_quadratic,Finset.expect_sum_comm]
  have hm (i j : ι) :
      (𝔼 ε : ι → Bool, (finiteSign ε i*finiteSign ε j) •
        ((P i).val.val*conjugationOperator J (P j).val.val))=
        (if i=j then 1 else 0 : ℝ) • ((P i).val.val*conjugationOperator J (P j).val.val) := by
    let L : ℝ →ₗ[ℚ≥0] (H →L[ℂ] H) :=
      (LinearMap.toSpanSingleton ℝ (H →L[ℂ] H)
        ((P i).val.val*conjugationOperator J (P j).val.val)).restrictScalars ℚ≥0
    have he := congrArg L (finiteSign_pair i j)
    rw [map_expect] at he
    exact he
  simp only [hm,ite_smul,one_smul,zero_smul]
  simp [modularQuadratic]

end

end KadisonKastler

end OAI
