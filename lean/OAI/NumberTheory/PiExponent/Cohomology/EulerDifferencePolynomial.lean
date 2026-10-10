import Mathlib

namespace OAI

namespace PiExponent.NumericalAmpleness

open Filter Finset Function
open scoped Topology BigOperators

theorem forwardDifference_eq_zero_of_le {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d] f = 0)
    (k : ℕ) (hk : d ≤ k) : (fwdDiff (1 : ℕ))^[k] f = 0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm d r, Function.iterate_add_apply, hzero]
  ext n
  simp [fwdDiff_iter_eq_sum_shift]

theorem newton_sum_of_forwardDifference_eq_zero {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (d+1), n.choose k • (fwdDiff (1 : ℕ))^[k] f 0 := by
  have hNewton : f n = ∑ k ∈ Finset.range (n+1),
      n.choose k • (fwdDiff (1 : ℕ))^[k] f 0 := by
    simpa using shift_eq_sum_fwdDiff_iter (1 : ℕ) f n 0
  rw [hNewton]
  by_cases hnd : n ≤ d
  · apply Finset.sum_subset (Finset.range_mono (by omega : n+1 ≤ d+1))
    intro k hk hkn
    have hnk : n < k := by simp only [Finset.mem_range] at hkn; omega
    rw [Nat.choose_eq_zero_of_lt hnk, zero_smul]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : d+1 ≤ n+1))
    intro k hk hkd
    have hdk : d+1 ≤ k := by simp only [Finset.mem_range] at hkd; omega
    rw [forwardDifference_eq_zero_of_le f (d+1) hzero k hdk]
    simp

theorem integer_newton_sum_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (d+1),
      (n.choose k : ℤ) * (fwdDiff (1 : ℕ))^[k] f 0 := by
  simpa only [nsmul_eq_mul] using newton_sum_of_forwardDifference_eq_zero f d hzero n

theorem tendsto_choose_div_pow (k d : ℕ) (hkd : k ≤ d) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ)^d) atTop
      (𝓝 (if k = d then 1 / (d.factorial : ℝ) else 0)) := by
  have he := (isEquivalent_choose k).div
    (Asymptotics.IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)^d) (l := atTop))
  apply he.symm.tendsto_nhds
  by_cases h : k = d
  · subst k
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    dsimp
    field_simp
  · simp only [h, ite_false]
    have ht := (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (lt_of_le_of_ne hkd h)).comp
      tendsto_natCast_atTop_atTop
    have ht' := ht.div_const (k.factorial : ℝ)
    change Tendsto (fun n : ℕ => (n : ℝ)^k / (k.factorial : ℝ) / (n : ℝ)^d) _ _
    convert ht' using 1
    · funext n
      simp only [Function.comp_apply]
      ring
    · simp

theorem tendsto_normalized_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)^d) atTop
      (𝓝 ((((fwdDiff (1 : ℕ))^[d] f 0 : ℤ) : ℝ) / (d.factorial : ℝ))) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (d+1)) :=
    (tendsto_choose_div_pow k d (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).mul_const
      (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℝ)
  have hs := tendsto_finsetSum (Finset.range (d+1)) hterm
  have hreal (n : ℕ) : (f n : ℝ) = ∑ k ∈ Finset.range (d+1),
      (n.choose k : ℝ) * (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℝ) := by
    exact_mod_cast integer_newton_sum_of_forwardDifference_eq_zero f d hzero n
  convert hs using 1
  · funext n
    rw [hreal, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · congr 1
    rw [Finset.sum_eq_single d]
    · simp only [ite_true]
      ring
    · intro k hk hkd
      simp [hkd]
    · simp

theorem tendsto_atTop_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hd : 0 < d)
    (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0)
    (hpositive : 0 < (fwdDiff (1 : ℕ))^[d] f 0) :
    Tendsto f atTop atTop := by
  have hlead : (0 : ℝ) <
      (((fwdDiff (1 : ℕ))^[d] f 0 : ℤ) : ℝ) / (d.factorial : ℝ) :=
    div_pos (by exact_mod_cast hpositive) (by exact_mod_cast Nat.factorial_pos d)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^d) atTop atTop :=
    (tendsto_pow_atTop (Nat.ne_of_gt hd)).comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_normalized_of_forwardDifference_eq_zero f d hzero).pos_mul_atTop
    hlead hpow
  apply (tendsto_intCast_atTop_iff (R := ℝ)).mp
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ)^d ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hn)
  exact div_mul_cancel₀ _ hn'

end PiExponent.NumericalAmpleness

end OAI
