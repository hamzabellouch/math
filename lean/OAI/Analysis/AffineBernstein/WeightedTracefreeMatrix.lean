import Mathlib
import OAI.Analysis.AffineBernstein.TracefreeMatrix

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Matrix
open scoped MatrixOrder

lemma weighted_tracefree_matrix_gap {n : ℕ} (hn : 1 ≤ n)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.IsHermitian)
    (htr : (A⁻¹*B).trace=0) :
    (((n:ℝ)*(A⁻¹*B*A⁻¹*B).trace) • A - ((n:ℝ)+1) • (B*A⁻¹*B)).PosSemidef := by
  let S := CFC.sqrt A⁻¹
  have hS : S.conjTranspose=S := (CFC.sqrt_nonneg A⁻¹).isSelfAdjoint
  have hSS : S*S=A⁻¹ := by simpa only [S,pow_two] using CFC.sq_sqrt A⁻¹ hA.inv.posSemidef.nonneg
  let C := S*B*S
  have hC : C.IsHermitian := by
    change (S*B*S).conjTranspose=S*B*S
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hS,hB,Matrix.mul_assoc]
  have hc0 : C.trace=0 := by
    dsimp only [C]
    rw [Matrix.trace_mul_cycle,hSS,htr]
  have hc2 : C*C=S*(B*A⁻¹*B)*S := by
    dsimp [C]
    calc
      _ = S*(B*(S*S)*B)*S := by noncomm_ring
      _ = _ := by rw [hSS]
  have hct : (C*C).trace=(A⁻¹*B*A⁻¹*B).trace := by
    rw [hc2,Matrix.trace_mul_cycle,hSS]
    simp only [Matrix.mul_assoc]
  have haI : A*A⁻¹=1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hIa : A⁻¹*A=1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hT : (A*S).conjTranspose=S*A := by rw [Matrix.conjTranspose_mul,hS,hA.isHermitian.eq]
  have hT1 : (A*S)*1*(S*A)=A := by
    rw [Matrix.mul_one]
    calc
      _ = A*(S*S)*A := by noncomm_ring
      _ = A := by rw [hSS,haI,Matrix.one_mul]
  have hT2 : (A*S)*(C*C)*(S*A)=B*A⁻¹*B := by
    rw [hc2]
    calc
      _ = (A*(S*S))*(B*A⁻¹*B)*((S*S)*A) := by noncomm_ring
      _ = _ := by rw [hSS,haI,hIa,Matrix.one_mul,Matrix.mul_one]
  have hh := (tracefree_matrix_gap hn hC hc0).mul_mul_conjTranspose_same (A*S)
  simpa only [hT,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hT1,hT2,hct] using hh

lemma weighted_tracefree_quadratic_gap {n : ℕ} (hn : 1 ≤ n)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.IsHermitian)
    (htr : (A⁻¹*B).trace=0) (e : Fin n → ℝ) :
    ((n:ℝ)+1)*(e ⬝ᵥ ((B*A⁻¹*B)*ᵥ e)) ≤
      (n:ℝ)*(e ⬝ᵥ (A*ᵥ e))*(A⁻¹*B*A⁻¹*B).trace := by
  have h := (weighted_tracefree_matrix_gap hn hA hB htr).dotProduct_mulVec_nonneg e
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul] at h
  nlinarith

end AffineBernstein

end

end OAI
