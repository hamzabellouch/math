import OAI.Probability.SLE.Gauge.BatchEntryOrder

namespace OAI

/-! The exact radius prescription leaves a full test interval and the
subsequent mixing gap between consecutive tests and before cleanup. -/
noncomputable section
open Set

namespace SLEExactGauge.Target

lemma entryPosition_lt_cleanup (κ : ℝ) (W : WienerLaw) {n : ℕ}
    (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n)
    {k : ℤ} {j : ℕ} (hj : j < multiplicity κ W n k) :
    entryPosition κ W (n,some (k,j)) < entryPosition κ W (n,none) := by
  classical
  let c := multiplicity κ W n
  let hs := multiplicity_support_finite κ W hn hm1 hJ
  have hk : k∈hs.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact (Nat.zero_le j).trans_lt hj
  have hz (i : ℤ) (hi : i∉hs.toFinset) : c i=0 := by
    have : ¬0<c i := by
      intro h
      exact hi (hs.mem_toFinset.mpr h)
    omega
  have hp : (∑' i, if i<k then c i else 0) = ∑ i∈hs.toFinset, if i<k then c i else 0 := by
    apply tsum_eq_sum
    intro i hi
    simp only [hz i hi,ite_self]
  have ht : (∑' i, c i) = ∑ i∈hs.toFinset, c i := by
    exact tsum_eq_sum (fun i hi => hz i hi)
  have hb : (∑' i, if i<k then c i else 0)+c k ≤ ∑' i, c i := by
    rw [hp,ht]
    have hP := Finset.sum_erase_add hs.toFinset (fun i => if i<k then c i else 0) hk
    have hT := Finset.sum_erase_add hs.toFinset c hk
    simp only [lt_self_iff_false,ite_false,add_zero] at hP
    rw [← hP,← hT]
    apply Nat.add_le_add_right
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  exact (Nat.add_lt_add_left hj _).trans_le hb

lemma entryRadius_gap_of_position_lt {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    {n : ℕ} (hn : 1≤n) {o o' : Option (ℤ × ℕ)}
    (hpos : entryPosition κ W (n,o) < entryPosition κ W (n,o')) :
    entryRadius κ W (n,o') ≤ entryRadius κ W (n,o) *
      Real.exp (-2*a κ*((batchLevel κ W n:ℝ)+(n:ℝ))) := by
  have hpN : entryPosition κ W (n,o)+1 ≤ entryPosition κ W (n,o') := hpos
  have hp : (entryPosition κ W (n,o):ℝ)+1 ≤ entryPosition κ W (n,o') := by exact_mod_cast hpN
  have hnR : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hcoef : 0 < 2*a κ*((batchLevel κ W n:ℝ)+(n:ℝ)) := by
    exact mul_pos (mul_pos (by norm_num) (internal_a_pos hκ)) (by positivity)
  unfold entryRadius
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hcoef.le (sub_nonneg.mpr hp)]

lemma entryRadius_cleanup_gap {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    {n : ℕ} (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n)
    {k : ℤ} {j : ℕ} (hj : j < multiplicity κ W n k) :
    entryRadius κ W (n,none) ≤ entryRadius κ W (n,some (k,j)) *
      Real.exp (-2*a κ*((batchLevel κ W n:ℝ)+(n:ℝ))) :=
  entryRadius_gap_of_position_lt hκ W hn (entryPosition_lt_cleanup κ W hn hm1 hJ hj)

end SLEExactGauge.Target

end

end OAI
