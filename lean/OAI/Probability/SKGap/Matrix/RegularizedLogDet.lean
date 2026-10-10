import Mathlib
import OAI.Probability.SKGap.Matrix.MatrixLogDet
import OAI.Probability.SKGap.Localization.FrobeniusSq

namespace OAI

section
noncomputable section
namespace SKGap.LogDet
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def regularizedGram (γ : ℝ) (M : Matrix ι ι ℝ) := Mᵀ*M+γ • 1

def regularizedLogDet (γ : ℝ) (M : Matrix ι ι ℝ) : ℝ :=
  Real.log (regularizedGram γ M).det/(Fintype.card ι:ℝ)

lemma regularizedGram_posDef {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    (regularizedGram γ M).PosDef := by
  exact Matrix.PosDef.posSemidef_add (by simpa using Matrix.posSemidef_conjTranspose_mul_self M)
    (Matrix.PosDef.one.smul hγ)

lemma regularizedGram_transpose (γ : ℝ) (M : Matrix ι ι ℝ) :
    (regularizedGram γ M)ᵀ=regularizedGram γ M := by
  simp [regularizedGram]

lemma frobenius_sq_trace (M : Matrix ι ι ℝ) : ‖M‖^2=(Mᵀ*M).trace := by
  rw [SKGap.frobenius_sq]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [sq]

lemma trace_inner_abs (M H : Matrix ι ι ℝ) : |(Mᵀ*H).trace| ≤ ‖M‖*‖H‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι×ι))
    (fun p => M p.1 p.2) (fun p => H p.1 p.2)
  simp only [Fintype.sum_prod_type] at hc
  have ht : (Mᵀ*H).trace=∑ i,∑ k,M i k*H i k := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
    exact Finset.sum_comm
  rw [ht]
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← sq,sq_abs,mul_pow,SKGap.frobenius_sq] using hc

lemma regularized_resolvent_square {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    let Q := regularizedGram γ M
    (1-(2*γ) • Q⁻¹)ᵀ*(1-(2*γ) • Q⁻¹)=1-(4*γ) • ((M*Q⁻¹)ᵀ*(M*Q⁻¹)) := by
  dsimp only
  let Q := regularizedGram γ M
  have hQ := regularizedGram_posDef hγ M |>.isUnit
  have hi : Q⁻¹*Q=1 := Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det _).mp hQ)
  have ht : (Q⁻¹)ᵀ=Q⁻¹ := by rw [Matrix.transpose_nonsing_inv,regularizedGram_transpose]
  have he : Q⁻¹*(Mᵀ*M)*Q⁻¹=Q⁻¹-γ • (Q⁻¹*Q⁻¹) := by
    have h := congrArg (fun X : Matrix ι ι ℝ => X*Q⁻¹) hi
    dsimp only [Q,regularizedGram] at h ⊢
    simp only [mul_add,Matrix.mul_smul,mul_one,add_mul,Matrix.smul_mul,one_mul] at h
    exact eq_sub_of_add_eq h
  change (1-(2*γ) • Q⁻¹)ᵀ*(1-(2*γ) • Q⁻¹)=1-(4*γ) • ((M*Q⁻¹)ᵀ*(M*Q⁻¹))
  simp only [Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_smul,ht,
    Matrix.transpose_mul,one_sub_mul,mul_sub,mul_one,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have he' : Q⁻¹*Mᵀ*(M*Q⁻¹)=Q⁻¹-γ • (Q⁻¹*Q⁻¹) := by simpa only [mul_assoc] using he
  rw [he',smul_sub,smul_smul]
  module

lemma regularized_resolvent_frobenius {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    4*γ*‖M*(regularizedGram γ M)⁻¹‖^2 ≤ (Fintype.card ι:ℝ) := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self
    (1-(2*γ) • (regularizedGram γ M)⁻¹)
  have ht := hp.trace_nonneg
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at ht
  rw [regularized_resolvent_square hγ M,Matrix.trace_sub,Matrix.trace_smul,
    Matrix.trace_one,smul_eq_mul,← frobenius_sq_trace] at ht
  linarith

lemma hasDerivAt_regularizedGram (γ : ℝ) (M H : Matrix ι ι ℝ) (t : ℝ) (i k : ι) :
    HasDerivAt (fun s : ℝ => regularizedGram γ (M+s • H) i k)
      ((Hᵀ*(M+t • H)+(M+t • H)ᵀ*H) i k) t := by
  have h (a b : ι) : HasDerivAt (fun s : ℝ => (M+s • H) a b) (H a b) t := by
    convert ((hasDerivAt_id t).mul_const (H a b)).const_add (M a b) using 1 <;> first | rfl | simp
  have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (h l i).mul (h l k))).add_const ((γ • (1:Matrix ι ι ℝ)) i k)
  convert hh using 1 <;> try rfl
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_add_distrib]

lemma trace_regularized_derivative (M H K : Matrix ι ι ℝ) (hK : Kᵀ=K) :
    ((Hᵀ*M+Mᵀ*H)*K).trace=2*((M*K)ᵀ*H).trace := by
  rw [add_mul,Matrix.trace_add]
  have h₁ : (Hᵀ*M*K).trace=((M*K)ᵀ*H).trace := by
    rw [← Matrix.trace_transpose (Hᵀ*M*K)]
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hK,mul_assoc]
  have h₂ : (Mᵀ*H*K).trace=((M*K)ᵀ*H).trace := by
    rw [Matrix.trace_mul_cycle]
    simp only [Matrix.transpose_mul,hK]
  rw [h₁,h₂]
  ring

lemma hasDerivAt_regularizedLogDet (γ : ℝ) (hγ : 0 < γ) (M H : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => regularizedLogDet γ (M+s • H))
      (2*(((M+t • H)*(regularizedGram γ (M+t • H))⁻¹)ᵀ*H).trace/(Fintype.card ι:ℝ)) t := by
  have hh := (hasDerivAt_logdet (hasDerivAt_regularizedGram γ M H t)
    (regularizedGram_posDef hγ (M+t • H)).isUnit).div_const (Fintype.card ι:ℝ)
  rw [trace_regularized_derivative] at hh
  · exact hh
  · rw [Matrix.transpose_nonsing_inv,regularizedGram_transpose]

lemma regularized_gradient_bound [Nonempty ι] {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    2*‖M*(regularizedGram γ M)⁻¹‖/(Fintype.card ι:ℝ) ≤ 1/sqrt ((Fintype.card ι:ℝ)*γ) := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hg : 0 < (Fintype.card ι:ℝ)*γ := mul_pos hn hγ
  apply (div_le_div_iff₀ hn (sqrt_pos.mpr hg)).mpr
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq hn.le
  simpa only [← sq,mul_pow,sq_sqrt hg.le] using
    (show (2*‖M*(regularizedGram γ M)⁻¹‖)^2*((Fintype.card ι:ℝ)*γ) ≤ (Fintype.card ι:ℝ)^2 by
      have hh := mul_le_mul_of_nonneg_left (regularized_resolvent_frobenius hγ M) hn.le
      nlinarith only [hh])

lemma regularized_derivative_bound [Nonempty ι] {γ : ℝ} (hγ : 0 < γ) (M H : Matrix ι ι ℝ) :
    |2*((M*(regularizedGram γ M)⁻¹)ᵀ*H).trace/(Fintype.card ι:ℝ)| ≤
      1/sqrt ((Fintype.card ι:ℝ)*γ)*‖H‖ := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [abs_div,abs_mul,abs_of_pos hn,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*(‖M*(regularizedGram γ M)⁻¹‖*‖H‖)/(Fintype.card ι:ℝ) := by
      gcongr
      exact trace_inner_abs _ _
    _ = (2*‖M*(regularizedGram γ M)⁻¹‖/(Fintype.card ι:ℝ))*‖H‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (regularized_gradient_bound hγ M) (norm_nonneg _)

theorem regularizedLogDet_lipschitz [Nonempty ι] {γ : ℝ} (hγ : 0 < γ)
    (M N : Matrix ι ι ℝ) :
    |regularizedLogDet γ M-regularizedLogDet γ N| ≤
      1/sqrt ((Fintype.card ι:ℝ)*γ)*‖M-N‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := fun t : ℝ => regularizedLogDet γ (N+t • (M-N)))
    (f' := fun t => 2*(((N+t • (M-N))*(regularizedGram γ (N+t • (M-N)))⁻¹)ᵀ*(M-N)).trace/(Fintype.card ι:ℝ))
    (fun t _ => (hasDerivAt_regularizedLogDet γ hγ N (M-N) t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using regularized_derivative_bound hγ (N+t • (M-N)) (M-N))
    (convex_univ) (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel,sub_zero,norm_one,mul_one,Real.norm_eq_abs] using hh
end SKGap.LogDet
end
end

section
noncomputable section
namespace SKGap.LogDet
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma logdet_le_trace_sub_card {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    log M.det ≤ M.trace-(Fintype.card ι:ℝ) := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues,hM.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hM.eigenvalues_pos i))]
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Real.log_le_sub_one_of_pos (hM.eigenvalues_pos i))
  simpa using ht

lemma regularized_factorization (γ : ℝ) (M : Matrix ι ι ℝ) (hM : IsUnit M) :
    regularizedGram γ M=Mᵀ*(1+γ • (M⁻¹ᵀ*M⁻¹))*M := by
  have hi := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have h₁ := Matrix.nonsing_inv_mul M hi
  have h₂ : Mᵀ*M⁻¹ᵀ=1 := by rw [← Matrix.transpose_mul,h₁,transpose_one]
  unfold regularizedGram
  simp only [mul_add,add_mul,mul_one,Matrix.mul_smul,Matrix.smul_mul]
  rw [← mul_assoc Mᵀ M⁻¹ᵀ,h₂,one_mul,h₁]

lemma regularizedLogDet_le_logdet {γ : ℝ} (hγ : 0 ≤ γ) (M : Matrix ι ι ℝ) (hM : IsUnit M) :
    regularizedLogDet γ M ≤ 2*log M.det/(Fintype.card ι:ℝ)+
      γ*‖M⁻¹‖^2/(Fintype.card ι:ℝ) := by
  let Q := 1+γ • (M⁻¹ᵀ*M⁻¹)
  have hQ : Q.PosDef := Matrix.PosDef.one.add_posSemidef (by
    simpa using (Matrix.posSemidef_conjTranspose_mul_self M⁻¹).smul hγ)
  have hd : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M).mp hM |>.ne_zero
  have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hl : log (regularizedGram γ M).det=2*log M.det+log Q.det := by
    rw [regularized_factorization γ M hM,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
      Real.log_mul (mul_ne_zero hd hQ.det_pos.ne') hd,Real.log_mul hd hQ.det_pos.ne']
    ring
  have ht := logdet_le_trace_sub_card hQ
  have hQt : Q.trace-(Fintype.card ι:ℝ)=γ*‖M⁻¹‖^2 := by
    dsimp only [Q]
    rw [Matrix.trace_add,Matrix.trace_one,Matrix.trace_smul,smul_eq_mul,← frobenius_sq_trace]
    ring
  rw [hQt] at ht
  unfold regularizedLogDet
  rw [hl,add_div]
  exact add_le_add_right (div_le_div_of_nonneg_right ht hn) _

lemma frobenius_le_sqrt_card_opNorm (M : Matrix ι ι ℝ) :
    ‖M‖ ≤ sqrt (Fintype.card ι:ℝ)*opNorm M := by
  have hh := SKGap.frobenius_mul_le_opNorm_right (1:Matrix ι ι ℝ) M
  have h1 : ‖(1:Matrix ι ι ℝ)‖=sqrt (Fintype.card ι:ℝ) := by
    have hs := frobenius_sq_trace (1:Matrix ι ι ℝ)
    simp only [transpose_one,one_mul,Matrix.trace_one] at hs
    nlinarith [norm_nonneg (1:Matrix ι ι ℝ),sqrt_nonneg (Fintype.card ι:ℝ),sq_sqrt (Nat.cast_nonneg (Fintype.card ι))]
  simpa only [one_mul,h1] using hh

lemma regularizedLogDet_le_logdet_opNorm [Nonempty ι] {γ B : ℝ} (hγ : 0 ≤ γ)
    (M : Matrix ι ι ℝ) (hM : IsUnit M) (hB : opNorm M⁻¹ ≤ B) :
    regularizedLogDet γ M ≤ 2*log M.det/(Fintype.card ι:ℝ)+γ*B^2 := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hb0 : 0 ≤ B := (norm_nonneg _).trans hB
  apply (regularizedLogDet_le_logdet hγ M hM).trans
  apply add_le_add_right
  apply (div_le_iff₀ hn).mpr
  have hf := (frobenius_le_sqrt_card_opNorm M⁻¹).trans (mul_le_mul_of_nonneg_left hB (sqrt_nonneg _))
  have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) hb0) |>.mpr hf
  rw [mul_pow,sq_sqrt hn.le] at hsq
  nlinarith [mul_le_mul_of_nonneg_left hsq hγ]

lemma regularizedLogDet_zero [Nonempty ι] {γ : ℝ} (_hγ : 0 < γ) :
    regularizedLogDet γ (0:Matrix ι ι ℝ)=log γ := by
  have hn : (Fintype.card ι:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [regularizedLogDet,regularizedGram,transpose_zero,zero_mul,zero_add,
    Matrix.det_smul,Matrix.det_one,mul_one,Real.log_pow]
  exact mul_div_cancel_left₀ _ hn

lemma regularizedLogDet_abs [Nonempty ι] {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    |regularizedLogDet γ M| ≤ |log γ|+‖M‖/sqrt ((Fintype.card ι:ℝ)*γ) := by
  have hh := regularizedLogDet_lipschitz hγ M 0
  rw [sub_zero,regularizedLogDet_zero hγ] at hh
  have ht := (show |regularizedLogDet γ M| ≤ |regularizedLogDet γ M-log γ|+|log γ| by
    simpa only [sub_add_cancel] using abs_add_le (regularizedLogDet γ M-log γ) (log γ)).trans (add_le_add_left hh _)
  simpa only [div_eq_mul_inv,one_mul,mul_comm,add_comm] using ht
end SKGap.LogDet
end
end

end OAI
