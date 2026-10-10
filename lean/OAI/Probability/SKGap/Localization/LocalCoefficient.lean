import Mathlib
import OAI.Probability.SKGap.Localization.CoefficientFlip
import OAI.Probability.SKGap.Matrix.DiscreteMatrixCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

abbrev Args := ι⊕κ→ℝ

def localArgs (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i : Fin n) : Args (ι:=ι) (κ:=κ) :=
  Sum.elim (fun l=>H l x i) (fun α=>θ α x)

def partialAt (T : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ) (l : ι⊕κ) : ℝ := T (Pi.single l 1)

lemma linear_apply_coordinates {α : Type*} [Fintype α] [DecidableEq α]
    (T : (α→ℝ)→L[ℝ]ℝ) (v : α→ℝ) : T v=∑l,v l*T (Pi.single l 1) := by
  have he : v=∑l,v l • Pi.single l (1:ℝ) := by
    funext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [he]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma flipHalfDiff_coordinate {α : Type*} [Fintype α] (P : Spin n→α→ℝ)
    (k : Fin n) (x : Spin n) (l : α) :
    flipHalfDiff k P x l=halfDiff k (fun y=>P y l) x := by
  rw [halfDiff_as_flip]
  dsimp only [flipHalfDiff,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  ring

lemma coefficient_chain (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i k : Fin n)
    (T : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ) :
    T (flipHalfDiff k (fun y=>localArgs H θ y i) x)=
      (∑l,partialAt T (.inl l)*derivativeMatrix (H l) x i k)+
      ∑α,partialAt T (.inr α)*halfDiff k (θ α) x := by
  rw [linear_apply_coordinates,Fintype.sum_sum_type]
  simp only [flipHalfDiff_coordinate,partialAt,localArgs,Sum.elim_inl,Sum.elim_inr,derivativeMatrix,mul_comm]

omit [DecidableEq ι] [DecidableEq κ] in
lemma local_argument_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i k : Fin n) :
    ‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖ ≤
      (∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|) := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg
    (Finset.sum_nonneg fun l _=>abs_nonneg _) (Finset.sum_nonneg fun α _=>abs_nonneg _))).mpr
  intro l
  rw [Real.norm_eq_abs,flipHalfDiff_coordinate]
  cases l with
  | inl l =>
    dsimp only [localArgs,Sum.elim_inl]
    exact (Finset.single_le_sum (fun l _=>abs_nonneg (derivativeMatrix (H l) x i k)) (Finset.mem_univ l)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun α _=>abs_nonneg _))
  | inr α =>
    dsimp only [localArgs,Sum.elim_inr]
    exact (Finset.single_le_sum (fun α _=>abs_nonneg (halfDiff k (θ α) x)) (Finset.mem_univ α)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun l _=>abs_nonneg _))

def coefficient (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ) : VectorFields n :=
  fun x i=>F i (localArgs H θ x i)

def localPartial (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (l : ι⊕κ) : VectorFields n := fun x i=>partialAt (F' i (localArgs H θ x i)) l

def taylorError (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i k : Fin n) : ℝ :=
  derivativeMatrix (coefficient H θ F) x i k-
    F' i (localArgs H θ x i) (flipHalfDiff k (fun y=>localArgs H θ y i) x)

lemma source_derivative_exact (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) (i k : Fin n) :
    derivativeMatrix (fun x i=>coefficient H θ F x i*s x i) x i k=
      coefficient H θ F x i*derivativeMatrix s x i k+
      (∑l,s x i*localPartial H θ F' (.inl l) x i*derivativeMatrix (H l) x i k)+
      (∑α,s x i*localPartial H θ F' (.inr α) x i*halfDiff k (θ α) x)+
      s x i*taylorError H θ F F' x i k-
      2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k := by
  dsimp only [taylorError,localPartial]
  rw [coefficient_chain]
  simp only [←Finset.mul_sum,mul_assoc]
  rw [derivativeMatrix,halfDiff_mul]
  dsimp only [derivativeMatrix]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
lemma taylor_error_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i k : Fin n) {L Q T : ℝ} (hL : 0≤L) (hQ : 0≤Q) (hT : 0≤T)
    (hargs : ‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖≤Q+T)
    (hF : ∀t∈Set.Icc (0:ℝ) 1,HasFDerivAt (F i)
      (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (hLip : ∀t∈Set.Icc (0:ℝ) 1,
      ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))-
        F' i (localArgs H θ x i)‖≤L*‖t • (localArgs H θ (flip x k) i-localArgs H θ x i)‖) :
    |taylorError H θ F F' x i k|≤4*L*(Q^2+Q*T+T^2) := by
  have h:=coefficient_taylor k (fun y=>localArgs H θ y i) x (F i) (F' i) hL hF hLip
  have hs:=(pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg hQ hT)
    (by decide : 2 ≠ 0)).2 hargs
  have hh:=mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hL)
  change |taylorError H θ F F' x i k|≤_ at h
  refine h.trans (hh.trans ?_)
  nlinarith [sq_nonneg Q,sq_nonneg T,mul_nonneg hL (sq_nonneg Q),mul_nonneg hL (sq_nonneg T)]

end SKGapCutoff.Recipe

end
end

end OAI
