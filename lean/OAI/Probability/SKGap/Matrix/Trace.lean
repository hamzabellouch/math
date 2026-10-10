import Mathlib
import OAI.Probability.SKGap.Localization.LocalCoefficient
import OAI.Probability.SKGap.Localization.Operation

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

structure SegmentRegular (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (C : ℝ) : Prop where
  nonneg : 0≤C
  deriv : ∀i k t, t∈Set.Icc (0:ℝ) 1→HasFDerivAt (F i)
    (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))
  bound : ∀i k t, t∈Set.Icc (0:ℝ) 1→
    ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))‖≤C
  lip : ∀i k t, t∈Set.Icc (0:ℝ) 1→
    ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))-
      F' i (localArgs H θ x i)‖≤C*‖t • (localArgs H θ (flip x k) i-localArgs H θ x i)‖

lemma SegmentRegular.partial_bound {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {C : ℝ} (h : SegmentRegular H θ F F' x C) (i : Fin n) (l : ι⊕κ) :
    |localPartial H θ F' l x i|≤C := by
  have hb : ‖F' i (localArgs H θ x i)‖≤C := by simpa using h.bound i i 0 (by constructor <;> norm_num)
  have hs : ‖(Pi.single l (1:ℝ) : Args (ι:=ι) (κ:=κ))‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro a; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have h₁ := (F' i (localArgs H θ x i)).le_opNorm (Pi.single l 1)
  exact h₁.trans ((mul_le_mul hb hs (norm_nonneg _) h.nonneg).trans_eq (mul_one C))

def sourceError (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) : Interaction n :=
  derivativeMatrix (fun x i=>coefficient H θ F x i*s x i) x-
    Matrix.diagonal (coefficient H θ F x)*derivativeMatrix s x-
    ∑l,Matrix.diagonal (fun i=>s x i*localPartial H θ F' (.inl l) x i)*derivativeMatrix (H l) x

lemma sourceError_eq (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) :
    sourceError H θ F F' s x=
      (∑α,Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x))+
      Matrix.of (fun i k=>s x i*taylorError H θ F F' x i k)-
      Matrix.of (fun i k=>2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k) := by
  ext i k
  simp only [sourceError,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.sum_apply,Matrix.add_apply,Matrix.of_apply]
  rw [source_derivative_exact]
  ring

def primaryIncrement (H : ι→VectorFields n) (x : Spin n) : Interaction n :=
  fun i k=>∑l,|derivativeMatrix (H l) x i k|
def parameterIncrement (θ : κ→Spin n→ℝ) (x : Spin n) : Fin n→ℝ :=
  fun k=>∑α,|halfDiff k (θ α) x|

lemma sourceError_trace (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) (P : Interaction n) {C S T B R L O : ℝ}
    (h : SegmentRegular H θ F F' x C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B)
    (hR : 0≤R) (hL : 0≤L) (hO : 0≤O)
    (hs : vectorNorm (s x)≤S) (hds : ‖derivativeMatrix s x‖≤S)
    (ht : vectorNorm (parameterIncrement θ x)≤T)
    (hQ4 : (∑i,∑k,(primaryIncrement H x i k)^4)≤B^4)
    (hQr : ∀i,(∑k,(primaryIncrement H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement H x i i)^2)≤L^2)
    (hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤O^4) :
    |trace (P*sourceError H θ F F' s x)|≤
      SKGap.opNorm P*C*S*(∑α,‖derivativeVector (θ α) x‖)+
      4*C*SKGap.opNorm P*S*(B^2+R*T+T^2)+
      2*C*S*(O*B+SKGap.opNorm P*(L+T)) := by
  let Q := primaryIncrement H x
  let t := parameterIncrement θ x
  have hQ : ∀i k,0≤Q i k := fun i k=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have htt : ∀k,0≤t k := fun k=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hs2 : (∑i,(s x i)^2)≤S^2 := by rw [←vectorNorm_sq]; exact pow_le_pow_left₀ (vectorNorm_nonneg _) hs 2
  have ht2 : (∑k,(t k)^2)≤T^2 := by rw [←vectorNorm_sq]; exact pow_le_pow_left₀ (vectorNorm_nonneg _) ht 2
  have hds2 : (∑i,∑k,(derivativeMatrix s x i k)^2)≤S^2 := by
    rw [←SKGap.frobenius_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hds 2
  have htaylor := source_taylor_trace_bound P (Matrix.of (fun i k=>s x i*taylorError H θ F F' x i k)) Q (s x) t
    (mul_nonneg (by norm_num : (0:ℝ)≤4) h.nonneg) hS hT hB hR hs2 ht2 hQ4 hQr (by
      intro i k
      simp only [Matrix.of_apply,abs_mul,abs_of_nonneg (hQ i k),abs_of_nonneg (htt k)]
      have hh := taylor_error_bound H θ F F' x i k h.nonneg (hQ i k) (htt k)
        (local_argument_bound H θ x i k) (h.deriv i k) (h.lip i k)
      nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (s x i))])
  have hproduct := source_product_trace_bound P
    (Matrix.of (fun i k=>2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k))
    (derivativeMatrix s x) Q t (mul_nonneg (by norm_num : (0:ℝ)≤2) h.nonneg)
    hS hT hO hB hL hds2 ht2 hP hQ4 hQd (by
      intro i k
      simp only [Matrix.of_apply,abs_mul,abs_spin_eq_one,mul_one,abs_of_nonneg (hQ i k),abs_of_nonneg (htt k)]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hh := (coefficient_lipschitz k (fun y=>localArgs H θ y i) x (F i) (F' i)
        h.nonneg (h.deriv i k) (h.bound i k)).trans
          (mul_le_mul_of_nonneg_left (local_argument_bound H θ x i k) h.nonneg)
      change |derivativeMatrix (coefficient H θ F) x i k|≤C*(Q i k+t k) at hh
      nlinarith [mul_le_mul_of_nonneg_right hh (abs_nonneg (derivativeMatrix s x i k))])
  have hrank (α : κ) :
      |trace (P*Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x))|≤
        SKGap.opNorm P*C*S*‖derivativeVector (θ α) x‖ := by
    have hu : vectorNorm (fun i=>s x i*localPartial H θ F' (.inr α) x i)≤C*S := by
      have H₁ := (vectorNorm_mul (fun i=>localPartial H θ F' (.inr α) x i) (s x) h.nonneg
        (fun i=>h.partial_bound i (.inr α))).trans (mul_le_mul_of_nonneg_left hs h.nonneg)
      simpa only [mul_comm] using H₁
    have HH:=rank_one_trace_bound P
      (WithLp.toLp 2 (fun i=>s x i*localPartial H θ F' (.inr α) x i)) (derivativeVector (θ α) x)
    apply HH.trans
    change SKGap.opNorm P*vectorNorm _*‖derivativeVector (θ α) x‖≤_
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (real_op_norm_nonneg P))
      (norm_nonneg (derivativeVector (θ α) x))]
  have hranks : |trace (P*(∑α,Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x)))|≤
      SKGap.opNorm P*C*S*(∑α,‖derivativeVector (θ α) x‖) := by
    rw [Matrix.mul_sum,trace_sum]
    exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum fun α _=>hrank α).trans_eq (by rw [Finset.mul_sum]))
  rw [sourceError_eq,mul_sub,mul_add,trace_sub,trace_add]
  exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hranks htaylor)) hproduct)

end SKGapCutoff.Recipe

end
end

end OAI
