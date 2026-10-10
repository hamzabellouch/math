import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallMixing
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperOuterBudget

namespace OAI

/-! # Binary lengths for the small-chain capacity bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)

lemma stateBound_clog_le :
    Nat.clog 2 (stateBound r c+2) ≤ Nat.clog 2 ((∑ i,r i)+1)+20*d+2 := by
  have hd : 1 ≤ d := by unfold dimensionAllowance; omega
  have h13 : d^13 ≤ 2^(20*d) :=
    (nat_pow_le_two_pow d 13).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have h20 : d^20 ≤ 2^(20*d) := by simpa only [Nat.mul_comm] using nat_pow_le_two_pow d 20
  have h4 : 4 ≤ 2^(20*d) := by
    exact (by decide : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hrest : d*d^12+d^20+4 ≤ 2^(20*d+2) := by
    have he : d*d^12=d^13 := by ring
    rw [he,pow_add]
    norm_num
    omega
  have hpow : 1 ≤ 2^(20*d+2) := one_le_pow₀ (by decide)
  have hn := Nat.le_pow_clog (by decide : 1<2) ((∑ i,r i)+1)
  apply Nat.clog_le_of_le_pow
  calc
    stateBound r c+2=(∑ i,r i)+(d*d^12+d^20+4) := by unfold stateBound; omega
    _ ≤ (∑ i,r i)+2^(20*d+2) := Nat.add_le_add_left hrest _
    _ ≤ ((∑ i,r i)+1)*2^(20*d+2) := by
      have hm := Nat.mul_le_mul_left (∑ i,r i) hpow
      simpa only [mul_one,add_mul,one_mul] using Nat.add_le_add_right hm (2^(20*d+2))
    _ ≤ 2^(Nat.clog 2 ((∑ i,r i)+1))*2^(20*d+2) := Nat.mul_le_mul_right _ hn
    _ = 2^(Nat.clog 2 ((∑ i,r i)+1)+20*d+2) := by
      rw [←pow_add]
      congr 1

noncomputable def smallBinaryLength : ℕ := d+Nat.clog 2 (stateBound r c+2)

lemma smallBinaryLength_parameters :
    Nat.clog 2 (stateBound r c+2) ≤ smallBinaryLength r c ∧
    d ≤ smallBinaryLength r c ∧ stateBound r c+1 ≤ 2^(smallBinaryLength r c) := by
  refine ⟨by unfold smallBinaryLength; omega,by unfold smallBinaryLength; omega,?_⟩
  have hb : Nat.clog 2 (stateBound r c+2) ≤ smallBinaryLength r c := by
    unfold smallBinaryLength
    omega
  exact (show stateBound r c+1 ≤ stateBound r c+2 by omega).trans
    ((Nat.le_pow_clog (by decide) (stateBound r c+2)).trans
      (Nat.pow_le_pow_right (by decide) hb))

lemma smallBinaryLength_le :
    smallBinaryLength r c ≤ 21*d+Nat.clog 2 ((∑ i,r i)+1)+2 := by
  have h := stateBound_clog_le r c
  unfold smallBinaryLength
  omega

end ContingencyTables.SmallGraphProfiles

end OAI
