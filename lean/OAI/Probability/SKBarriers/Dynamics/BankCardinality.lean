import Mathlib
import OAI.Probability.SKBarriers.Dynamics.BankPool

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

def bankPrefix (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 => bankPrefix c j+c j+2

 theorem bankPrefix_nonneg (c : ℕ → ℝ) (hc : ∀j,0≤c j) (j : ℕ) : 0≤bankPrefix c j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => simp only [bankPrefix]; linarith only [ih,hc j]

 theorem bankPrefix_mono (c : ℕ → ℝ) (hc : ∀j,0≤c j) : Monotone (bankPrefix c) := by
  apply monotone_nat_of_le_succ
  intro j
  simp only [bankPrefix]
  linarith only [hc j]

 theorem bankPrefix_cost_le (c : ℕ → ℝ) (hc : ∀j,0≤c j) {j B : ℕ} (hj : j<B) : c j+2≤bankPrefix c B := by
  have h := bankPrefix_mono c hc (show j+1≤B by omega)
  simp only [bankPrefix] at h
  linarith only [h,bankPrefix_nonneg c hc j]

def blockPriorEquiv (p B : ℕ) (j : Fin p) : BankPrior (blockPrior p B) j ≃ Fin (j.val%B) where
  toFun i := ⟨i.val.val-j.val/B*B,by
    have h := (mem_blockPrior p B i.val j).mp i.property
    have hd : j.val%B+j.val/B*B=j.val := by simpa only [Nat.mul_comm] using Nat.mod_add_div j.val B
    omega⟩
  invFun a := ⟨⟨j.val/B*B+a.val,by
    have hd : j.val%B+j.val/B*B=j.val := by simpa only [Nat.mul_comm] using Nat.mod_add_div j.val B
    have h := j.isLt
    omega⟩,by
    apply (mem_blockPrior p B _ j).mpr
    have hd : j.val%B+j.val/B*B=j.val := by simpa only [Nat.mul_comm] using Nat.mod_add_div j.val B
    change j.val/B*B≤j.val/B*B+a.val ∧ j.val/B*B+a.val<j.val
    constructor <;> omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have h := (mem_blockPrior p B i.val j).mp i.property
    simp only
    omega
  right_inv a := by
    apply Fin.ext
    simp only
    omega

 theorem blockPriorEquiv_mod (p B : ℕ) (hB : 0<B) (j : Fin p) (a : Fin (j.val%B)) :
    ((blockPriorEquiv p B j).symm a).val.val%B=a.val := by
  change (j.val/B*B+a.val)%B=a.val
  rw [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt]
  exact a.isLt.trans (Nat.mod_lt _ hB)

 theorem bankPrefix_sum (c : ℕ → ℝ) (j : ℕ) : (∑i∈Finset.range j,(c i+2))=bankPrefix c j := by
  induction j with
  | zero => simp [bankPrefix]
  | succ j ih => rw [Finset.sum_range_succ,ih]; simp only [bankPrefix]; ring

 theorem bankTuple_card_bound {p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (K : Fin p → ℕ) (L : ℝ)
    (hK : ∀j,(K j:ℝ)≤Real.exp ((c (j.val%B)+2)*L)) (j : Fin p) :
    (Fintype.card (BankTuple K (blockPrior p B) j):ℝ)≤Real.exp (bankPrefix c (j.val%B)*L) := by
  have he : (Fintype.card (BankTuple K (blockPrior p B) j):ℝ)=
      ∏i : BankPrior (blockPrior p B) j,(K i.val:ℝ) := by
    simp only [BankTuple,Fintype.card_pi,Fintype.card_fin,Nat.cast_prod]
  rw [he]
  calc
    _ ≤ ∏i : BankPrior (blockPrior p B) j,Real.exp ((c (i.val.val%B)+2)*L) := by
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _; exact hK i.val
    _ = ∏a : Fin (j.val%B),Real.exp ((c a.val+2)*L) := by
      rw [← Equiv.prod_comp (blockPriorEquiv p B j).symm]
      apply Finset.prod_congr rfl
      intro a _
      rw [blockPriorEquiv_mod p B hB j a]
    _ = Real.exp (bankPrefix c (j.val%B)*L) := by
      rw [← Real.exp_sum,← Finset.sum_mul]
      congr 1
      have hs := Fin.sum_univ_eq_sum_range (fun i => c i+2) (j.val%B)
      rw [hs,bankPrefix_sum]

 theorem bankIndex_card_bound {p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0≤c j)
    (K : Fin p → ℕ) {L : ℝ} (hL : 0≤L)
    (hK : ∀j,(K j:ℝ)≤Real.exp ((c (j.val%B)+2)*L)) :
    (Fintype.card (BankIndex K):ℝ)≤p*Real.exp (bankPrefix c B*L) := by
  simp only [BankIndex,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  calc
    _ ≤ ∑_j : Fin p,Real.exp (bankPrefix c B*L) := by
      apply Finset.sum_le_sum
      intro j _
      exact (hK j).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (bankPrefix_cost_le c hc (Nat.mod_lt _ hB)) hL))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

 theorem ceil_exp_bound {c L : ℝ} (hc : 0≤c) (hL : 1≤L) :
    (⌈Real.exp ((c+1)*L)⌉₊:ℝ)≤Real.exp ((c+2)*L) := by
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos ((c+1)*L)).le
  have he0 : 1≤Real.exp ((c+1)*L) := Real.one_le_exp_iff.mpr (by positivity)
  have he1 : 2≤Real.exp L := by
    have h := Real.add_one_le_exp L
    linarith only [h,hL]
  have he : Real.exp ((c+2)*L)=Real.exp ((c+1)*L)*Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith only [hceil,he0,he1]

end SK.Analytic

end
end

end OAI
