import Mathlib
import OAI.Analysis.Commutator.Definitions
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma commutator_ball_bdd (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    BddAbove {r : ℝ | ∃ a : K →L[ℂ] K, a∈P ∧ ‖a‖ ≤ 1 ∧ r=‖Y*a-a*Y‖} := by
  refine ⟨2*‖Y‖,?_⟩
  rintro r ⟨a,_,ha,rfl⟩
  calc
    ‖Y*a-a*Y‖ ≤ ‖Y*a‖+‖a*Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖*‖a‖+‖a‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 2*‖Y‖ := by nlinarith [norm_nonneg Y]

lemma commutatorSeminorm_nonneg (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    0 ≤ commutatorSeminorm P Y :=
  le_csSup (commutator_ball_bdd P Y) ⟨0,zero_mem P,by simp,by simp⟩

lemma commutator_bound_unitball (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
    {a : K →L[ℂ] K} (ha : a∈P) (hn : ‖a‖ ≤ 1) :
    ‖Y*a-a*Y‖ ≤ commutatorSeminorm P Y :=
  le_csSup (commutator_ball_bdd P Y) ⟨a,ha,hn,rfl⟩

lemma commutator_bound (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
    {a : K →L[ℂ] K} (ha : a∈P) :
    ‖Y*a-a*Y‖ ≤ commutatorSeminorm P Y*‖a‖ := by
  by_cases hz : a=0
  · simp [hz]
  have hpos := norm_pos_iff.mpr hz
  have hn : ‖((‖a‖⁻¹:ℝ):ℂ) • a‖ ≤ 1 := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),inv_mul_cancel₀ hpos.ne']
  have hb := commutator_bound_unitball P Y (P.toStarSubalgebra.smul_mem ha (((‖a‖⁻¹:ℝ):ℂ))) hn
  have he : Y*(((‖a‖⁻¹:ℝ):ℂ) • a)-(((‖a‖⁻¹:ℝ):ℂ) • a)*Y=((‖a‖⁻¹:ℝ):ℂ) • (Y*a-a*Y) := by
    simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)] at hb
  have hh := mul_le_mul_of_nonneg_left hb hpos.le
  rw [←mul_assoc,mul_inv_cancel₀ hpos.ne',one_mul] at hh
  simpa only [mul_comm ‖a‖] using hh

def innerDerivation (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    P →L[ℂ] (K →L[ℂ] K) :=
  ({ toFun := fun a => Y*(a:K →L[ℂ] K)-(a:K →L[ℂ] K)*Y
     map_add' := by
       intro a b
       change Y*((a:K →L[ℂ] K)+b)-((a:K →L[ℂ] K)+b)*Y=
         (Y*a-(a:K →L[ℂ] K)*Y)+(Y*b-(b:K →L[ℂ] K)*Y)
       noncomm_ring
     map_smul' := by
       intro c a
       change Y*(c • (a:K →L[ℂ] K))-(c • (a:K →L[ℂ] K))*Y=c • (Y*a-(a:K →L[ℂ] K)*Y)
       simp only [mul_smul_comm,smul_mul_assoc,smul_sub] } :
    P →ₗ[ℂ] (K →L[ℂ] K)).mkContinuous (commutatorSeminorm P Y)
      (fun a => commutator_bound P Y a.property)

@[simp] lemma innerDerivation_apply (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (a : P) :
    innerDerivation P Y a=Y*(a:K →L[ℂ] K)-(a:K →L[ℂ] K)*Y := rfl

lemma innerDerivation_norm_le (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    ‖innerDerivation P Y‖ ≤ commutatorSeminorm P Y :=
  ContinuousLinearMap.opNorm_le_bound _ (commutatorSeminorm_nonneg P Y)
    (fun a => commutator_bound P Y a.property)

lemma innerDerivation_mul (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (a b : P) :
    innerDerivation P Y (a*b)=(innerDerivation P Y a).comp (b:K →L[ℂ] K)+
      (a:K →L[ℂ] K).comp (innerDerivation P Y b) := by
  change Y*((a:K →L[ℂ] K)*b)-(a:K →L[ℂ] K)*b*Y=
    (Y*a-(a:K →L[ℂ] K)*Y)*b+(a:K →L[ℂ] K)*(Y*b-(b:K →L[ℂ] K)*Y)
  noncomm_ring

omit [CompleteSpace K] in
@[simp] lemma diagonalAmplification_apply (h : ℕ) (Y : K →L[ℂ] K)
    (x : PiLp 2 (fun _ : Fin h => K)) (i : Fin h) : diagonalAmplification h Y x i=Y (x i) := by
  simp [diagonalAmplification]

omit [CompleteSpace K] in
@[simp] lemma matrixOperator_apply (h : ℕ) (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K))
    (x : PiLp 2 (fun _ : Fin h => K)) (i : Fin h) : matrixOperator h X x i=∑ j,X i j (x j) := by
  simp [matrixOperator]

lemma diagonalAmplification_adjoint (h : ℕ) (Y : K →L[ℂ] K) :
    (diagonalAmplification h Y).adjoint=diagonalAmplification h Y.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,diagonalAmplification_apply,ContinuousLinearMap.adjoint_inner_left]

end Kadison

end

end
end

end OAI
