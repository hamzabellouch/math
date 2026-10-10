import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Matrix.Trace

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma finite_sum_fourth (f : ι→ℝ) :
    (∑l,f l)^4≤(Fintype.card ι:ℝ)^3*∑l,(f l)^4 := by
  have h1:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=f)
  have h2:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun l=>(f l)^2)
  simp only [Finset.card_univ] at h1 h2
  have hsq:=pow_le_pow_left₀ (sq_nonneg (∑l,f l)) h1 2
  have hh:=mul_le_mul_of_nonneg_left h2 (sq_nonneg (Fintype.card ι:ℝ))
  simp only [←pow_mul] at hsq hh
  norm_num only [Nat.reduceMul] at hsq hh
  nlinarith only [hsq,hh]

lemma primaryIncrement_fourth (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,ShapeBound (derivativeMatrix (H l) x) P) :
    (∑i,∑k,(primaryIncrement H x i k)^4)≤(2*(Fintype.card ι:ℝ)*P)^4 := by
  have h1 : (∑i,∑k,(primaryIncrement H x i k)^4)≤
      (Fintype.card ι:ℝ)^3*∑l,∑i,∑k,(derivativeMatrix (H l) x i k)^4 := by
    calc
      _ ≤ ∑i,∑k,(Fintype.card ι:ℝ)^3*∑l,(derivativeMatrix (H l) x i k)^4 := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro k _
        simpa only [primaryIncrement,show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs] using finite_sum_fourth (fun l=>|derivativeMatrix (H l) x i k|)
      _ = _ := by
        simp_rw [←Finset.mul_sum]
        congr 1
        rw [show (∑i,∑k,∑l,(derivativeMatrix (H l) x i k)^4)=
            ∑i,∑l,∑k,(derivativeMatrix (H l) x i k)^4 from
          Finset.sum_congr rfl (fun i _=>Finset.sum_comm)]
        exact Finset.sum_comm
  have h2 : (∑l,∑i,∑k,(derivativeMatrix (H l) x i k)^4)≤(Fintype.card ι:ℝ)*(2*P^4) := by
    exact (Finset.sum_le_sum (fun l _=>fourth_sum_le hP (hH l))).trans_eq (by simp)
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hnn : 0≤(Fintype.card ι:ℝ)^4*P^4 := by positivity
  nlinarith only [h3,hnn]

lemma primaryIncrement_row (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,SKGap.opNorm (derivativeMatrix (H l) x)≤P) (i : Fin n) :
    (∑k,(primaryIncrement H x i k)^2)≤((Fintype.card ι:ℝ)*P)^2 := by
  have H₁ : vectorNorm (primaryIncrement H x i)≤(Fintype.card ι:ℝ)*P := by
    calc
      _ ≤ ∑l,vectorNorm (fun k=>|derivativeMatrix (H l) x i k|) := by
        convert! vectorNorm_sum (fun l k=>|derivativeMatrix (H l) x i k|) using 1
        congr 1; ext k; simp [primaryIncrement]
      _ ≤ ∑_l:ι,P := Finset.sum_le_sum fun l _=>by rw [vectorNorm_abs]; exact (row_vectorNorm_le_opNorm _ _).trans (hH l)
      _ = _ := by simp
  rw [←vectorNorm_sq]
  exact (pow_le_pow_iff_left₀ (vectorNorm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hP) (by decide : 2 ≠ 0)).2 H₁

lemma primaryIncrement_diagonal (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,SKGap.diagonalSeminorm (derivativeMatrix (H l) x)≤P) :
    (∑i,(primaryIncrement H x i i)^2)≤((Fintype.card ι:ℝ)*P)^2 := by
  have H₁ : vectorNorm (fun i=>primaryIncrement H x i i)≤(Fintype.card ι:ℝ)*P := by
    calc
      _ ≤ ∑l,vectorNorm (fun i=>|derivativeMatrix (H l) x i i|) := by
        convert! vectorNorm_sum (fun l i=>|derivativeMatrix (H l) x i i|) using 1
        congr 1; ext i; simp [primaryIncrement]
      _ ≤ ∑_l:ι,P := Finset.sum_le_sum fun l _=>by rw [vectorNorm_abs]; exact hH l
      _ = _ := by simp
  rw [←vectorNorm_sq]
  exact (pow_le_pow_iff_left₀ (vectorNorm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hP) (by decide : 2 ≠ 0)).2 H₁

lemma parameterIncrement_bound (θ : κ→Spin n→ℝ) (x : Spin n) :
    vectorNorm (parameterIncrement θ x)≤∑α,‖derivativeVector (θ α) x‖ := by
  calc
    _ ≤ ∑α,vectorNorm (fun k=>|halfDiff k (θ α) x|) := by
      convert! vectorNorm_sum (fun α k=>|halfDiff k (θ α) x|) using 1
      congr 1; ext k; simp [parameterIncrement]
    _ = _ := by apply Finset.sum_congr rfl; intro α _; rw [vectorNorm_abs]; rfl

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
variable {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
variable {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
variable {x : Spin n} {C : ℝ}

lemma SegmentRegular.partial_difference (h : SegmentRegular H θ F F' x C)
    (l : ι⊕κ) (i k : Fin n) :
    |derivativeMatrix (localPartial H θ F' l) x i k|≤
      C*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖ := by
  have hv : ‖(Pi.single l 1 : Args (ι:=ι) (κ:=κ))‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro a; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have hh:=h.lip i k 1 (by constructor <;> norm_num)
  simp only [one_smul,add_sub_cancel] at hh
  have H₁ := (F' i (localArgs H θ (flip x k) i)-F' i (localArgs H θ x i)).le_opNorm (Pi.single l 1)
  have H₂ : |localPartial H θ F' l (flip x k) i-localPartial H θ F' l x i|≤
      C*‖localArgs H θ (flip x k) i-localArgs H θ x i‖ := by
    apply H₁.trans
    exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by simpa only [mul_one] using hh)
  rw [derivativeMatrix,halfDiff_as_flip,abs_div,abs_mul,abs_spin_eq_one,one_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm,abs_sub_comm]
  exact (div_le_div_of_nonneg_right H₂ (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

lemma SegmentRegular.partial_row (h : SegmentRegular H θ F F' x C) (l : ι⊕κ) (i : Fin n) :
    vectorNorm (derivativeMatrix (localPartial H θ F' l) x i)≤
      C*((∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)) := by
  calc
    _ ≤ vectorNorm (fun k=>C*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) :=
      vectorNorm_mono fun k=>by
        rw [abs_of_nonneg (mul_nonneg h.nonneg (norm_nonneg _))]
        exact h.partial_difference l i k
    _ = C*vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) := by
      convert! vectorNorm_smul C (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) using 1
      rw [abs_of_nonneg h.nonneg]
    _ ≤ _ := mul_le_mul_of_nonneg_left (local_argument_row_bound H θ x i) h.nonneg

omit [DecidableEq ι] [DecidableEq κ] in
lemma SegmentRegular.coefficient_bound (h : SegmentRegular H θ F F' x C)
    {A G : ℝ} (hA : 0≤A) (hG : 0≤G) (hv : ∀i,|coefficient H θ F x i|≤A)
    (hg : (∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)≤G) :
    CoefficientBound (coefficient H θ F) x A (C*G) := by
  refine ⟨hA,mul_nonneg h.nonneg hG,hv,?_⟩
  intro i
  have H₁ := (coefficient_row_bound H θ F F' x i h.nonneg (h.deriv i) (h.bound i)).trans
    (mul_le_mul_of_nonneg_left hg h.nonneg)
  rw [←vectorNorm_sq]
  exact pow_le_pow_left₀ (vectorNorm_nonneg _) H₁ 2

lemma SegmentRegular.partial_bound_coefficient (h : SegmentRegular H θ F F' x C)
    (l : ι⊕κ) {A G : ℝ} (hA : 0≤A) (hG : 0≤G) (hCA : C≤A)
    (hg : (∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)≤G) :
    CoefficientBound (localPartial H θ F' l) x A (C*G) := by
  refine ⟨hA,mul_nonneg h.nonneg hG,fun i=>(h.partial_bound i l).trans hCA,?_⟩
  intro i
  have H₁ := (h.partial_row l i).trans (mul_le_mul_of_nonneg_left hg h.nonneg)
  rw [←vectorNorm_sq]
  exact pow_le_pow_left₀ (vectorNorm_nonneg _) H₁ 2

end SKGapCutoff.Recipe

end
end

end OAI
