import Mathlib
import OAI.Combinatorics.UniformKServer.TreeRounding

namespace OAI

                                  
section

/-! Park conservation, subtree-cut capacities, and weighted park variation. -/
noncomputable section
namespace UniformKServer.TreeParking
open Finset TreeRounding
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem weighted_identity (q g : Vertex n → ℝ) :
    (∑ v, g v*park S q v)=∑ v, (g v*q v-if v=0 then 0 else g (S.parent v)*q v) := by
  simp only [park,mul_sub,sum_sub_distrib]
  rw [weighted_children]

theorem total (a : Allocation S k) : (∑ v, park S a.amount v)=k := by
  have h := weighted_identity (S:=S) a.amount (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  have he (v : Vertex n) : a.amount v-(if v=0 then 0 else a.amount v)=if v=0 then a.amount 0 else 0 := by
    split_ifs with hv
    · simp [hv]
    · simp
  simp only [he,sum_ite_eq',mem_univ,ite_true,a.root]

def boundary (A : Finset (Vertex n)) : Finset (Vertex n) := A.filter (fun v => v=0 ∨ S.parent v ∉ A)

theorem cut (a : Allocation S k) (A : Finset (Vertex n))
    (hc : ∀ v, v ≠ 0 → S.parent v ∈ A → v ∈ A) :
    (∑ v ∈ A, park S a.amount v)=∑ v ∈ boundary (S:=S) A, a.amount v := by
  have h := weighted_identity (S:=S) a.amount (fun v => if v ∈ A then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul] at h
  have he (v : Vertex n) :
      (if v ∈ A then a.amount v else 0)-(if v=0 then 0 else if S.parent v ∈ A then a.amount v else 0)=
      if v ∈ boundary (S:=S) A then a.amount v else 0 := by
    by_cases h0 : v=0
    · simp [h0,boundary]
    · by_cases hv : v ∈ A
      · by_cases hp : S.parent v ∈ A <;> simp [h0,hv,hp,boundary]
      · have hp : S.parent v ∉ A := fun hp => hv (hc v h0 hp)
        simp [h0,hv,hp,boundary]
  simp_rw [he] at h
  simpa only [←sum_filter,filter_mem_eq_inter,univ_inter] using h

theorem cut_capacity (a : Allocation S k) (T A : Finset (Vertex n)) (hTA : T ⊆ A)
    (hc : ∀ v, v ≠ 0 → S.parent v ∈ A → v ∈ A) :
    (∑ v ∈ T, park S a.amount v) ≤ ∑ v ∈ boundary (S:=S) A, a.amount v := by
  rw [←cut a A hc]
  exact sum_le_sum_of_subset_of_nonneg hTA (fun v _ _ => a.park_nonneg v)

theorem pointwise_variation (a b : Allocation S k) (v : Vertex n) :
    |park S b.amount v-park S a.amount v| ≤
      |b.amount v-a.amount v|+∑ i : Children S v, |b.amount i.val-a.amount i.val| := by
  have he : park S b.amount v-park S a.amount v=
      (b.amount v-a.amount v)-∑ i : Children S v, (b.amount i.val-a.amount i.val) := by
    simp only [park,sum_sub_distrib]; ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)

theorem weighted_variation (a b : Allocation S k) (w : Vertex n → ℝ) (τ : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hτ : 0 < τ)
    (hsep : ∀ v, v ≠ 0 → τ*w v ≤ w (S.parent v)) :
    (∑ v, w v*|park S b.amount v-park S a.amount v|) ≤
      (1+1/τ)*variation w a b := by
  have h₁ : (∑ v, w v*|b.amount v-a.amount v|) ≤ (1/τ)*variation w a b := by
    unfold variation
    rw [mul_sum]
    apply sum_le_sum
    intro v _
    by_cases hv : v=0
    · simp [hv,a.root,b.root]
    · simp only [ite_eq_right hv]
      have hs : w v ≤ (1/τ)*w (S.parent v) := by
        have hh := (le_div_iff₀ hτ).2 (show w v*τ ≤ w (S.parent v) by simpa [mul_comm] using hsep v hv)
        simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh
      nlinarith [mul_le_mul_of_nonneg_right hs (abs_nonneg (b.amount v-a.amount v))]
  calc
    _ ≤ ∑ v, w v*(|b.amount v-a.amount v|+∑ i : Children S v, |b.amount i.val-a.amount i.val|) :=
      sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (pointwise_variation a b v) (hw v)
    _ = (∑ v, w v*|b.amount v-a.amount v|)+variation w a b := by
      simp only [mul_add,sum_add_distrib]
      rw [weighted_children S w (fun v => |b.amount v-a.amount v|)]
      rfl
    _ ≤ _ := by linarith

end UniformKServer.TreeParking

end


end

end OAI
