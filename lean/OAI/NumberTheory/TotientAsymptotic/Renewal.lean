import OAI.NumberTheory.TotientAsymptotic.Basic

namespace OAI

/-! Existence, uniqueness and positivity of the renewal parameters. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma a_eq_integral (j : ℕ) :
    a j = ∫ t in (j : ℝ)..(j+1 : ℝ), Real.log t := by
  rw [integral_log]
  unfold a
  ring

lemma a_pos {j : ℕ} (hj : 1 ≤ j) : 0 < a j := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [a_eq_integral]
  apply intervalIntegral.integral_pos (by linarith)
  · exact continuousOn_id.log fun x hx => by
      change x ≠ 0
      exact ne_of_gt (by linarith [hx.1])
  · intro x hx
    exact (Real.log_pos (by linarith [hx.1])).le
  · exact ⟨j+1, ⟨by linarith, le_rfl⟩, Real.log_pos (by linarith)⟩

lemma a_le_log {j : ℕ} (hj : 1 ≤ j) : a j ≤ Real.log (j+1 : ℝ) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [a_eq_integral]
  have hh := intervalIntegral.integral_mono_on (a := (j : ℝ)) (b := (j+1 : ℝ))
    (by linarith) intervalIntegral.intervalIntegrable_log'
    (intervalIntegrable_const (c := Real.log (j+1 : ℝ)))
    (fun x hx => Real.log_le_log (by linarith [hx.1]) hx.2)
  simpa using hh

lemma a_le_index {j : ℕ} (hj : 1 ≤ j) : a j ≤ (j : ℝ) := by
  have hh := Real.log_le_sub_one_of_pos (x := (j+1 : ℝ)) (by positivity)
  exact (a_le_log hj).trans (by linarith)

def renewalSeries (r : ℝ) : ℝ := ∑' n : ℕ, a (n+1) * r^(n+1)

lemma summable_index_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    Summable (fun n : ℕ => (n+1 : ℝ)^k * r^(n+1)) := by
  have hh : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^k * r^(n+1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^k * r^n) 1).2
    (summable_pow_mul_geometric_of_norm_lt_one k
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1))
  simpa only [Nat.cast_add, Nat.cast_one] using hh

lemma summable_renewal {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => a (n+1) * r^(n+1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (a_pos (by omega)).le (pow_nonneg hr0 _))
    (fun n => mul_le_mul_of_nonneg_right (a_le_index (by omega)) (pow_nonneg hr0 _))
  simpa using summable_index_geometric hr0 hr1 1

lemma renewalSeries_continuousOn {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn renewalSeries (Set.Icc 0 r) := by
  apply continuousOn_tsum (u := fun n : ℕ => (n+1 : ℝ) * r^(n+1))
  · intro n
    fun_prop
  · simpa using summable_index_geometric hr0 hr1 1
  · intro n z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (a_pos (by omega)).le
      (pow_nonneg hz.1 _))]
    exact mul_le_mul (by exact_mod_cast a_le_index (j := n+1) (by omega))
      (pow_le_pow_left₀ hz.1 hz.2 _) (pow_nonneg hz.1 _) (by positivity)

lemma renewalSeries_strictMonoOn : StrictMonoOn renewalSeries (Set.Ico 0 1) := by
  intro x hx y hy hxy
  apply Summable.tsum_lt_tsum (i := 0)
  · intro n
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy.le _) (a_pos (by omega)).le
  · simpa using mul_lt_mul_of_pos_left hxy (a_pos (j := 1) le_rfl)
  · exact summable_renewal hx.1 hx.2
  · exact summable_renewal hy.1 hy.2

@[simp] lemma renewalSeries_zero : renewalSeries 0 = 0 := by
  simp [renewalSeries]

lemma renewalSeries_nine_tenths_gt_one : 1 < renewalSeries (9/10) := by
  have hs := summable_renewal (r := 9/10) (by norm_num) (by norm_num)
  have h := hs.sum_le_tsum (Finset.range 2)
    (fun n _ => mul_nonneg (a_pos (by omega)).le (pow_nonneg (by norm_num) _))
  change _ ≤ renewalSeries (9/10) at h
  norm_num [Finset.sum_range_succ, a] at h
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem renewal_root_exists_unique : ∃! z : ℝ, z ∈ RenewalRootSet := by
  have hc := renewalSeries_continuousOn (r := 9/10) (by norm_num) (by norm_num)
  obtain ⟨z, hz, heq⟩ := intermediate_value_Icc (a := (0 : ℝ)) (b := 9/10)
    (by norm_num) hc ⟨by simp, renewalSeries_nine_tenths_gt_one.le⟩
  have hz0 : 0 < z := by
    have hz_ne : z ≠ 0 := by
      intro h
      subst z
      simp at heq
    exact lt_of_le_of_ne hz.1 (Ne.symm hz_ne)
  have hz1 : z < 1 := lt_of_le_of_lt hz.2 (by norm_num)
  refine ⟨z, ⟨hz0, hz1, heq⟩, ?_⟩
  intro y hy
  have hy' : renewalSeries y = renewalSeries z := hy.2.2.trans heq.symm
  exact renewalSeries_strictMonoOn.injOn ⟨hy.1.le, hy.2.1⟩ ⟨hz0.le, hz1⟩ hy'

lemma rho_mem : rho ∈ RenewalRootSet := by
  obtain ⟨z, hz, hzunique⟩ := renewal_root_exists_unique
  have hs : RenewalRootSet = {z} := Set.eq_singleton_iff_unique_mem.mpr ⟨hz, hzunique⟩
  unfold rho
  rw [hs, csInf_singleton]
  simp

lemma rho_pos : 0 < rho := rho_mem.1
lemma rho_lt_one : rho < 1 := rho_mem.2.1
lemma renewalSeries_rho : renewalSeries rho = 1 := rho_mem.2.2

lemma lam_pos : 0 < lam := by
  apply Real.log_pos
  exact (lt_div_iff₀ rho_pos).2 (by simpa using rho_lt_one)

lemma summable_moment :
    Summable (fun n : ℕ => (n+1 : ℝ) * a (n+1) * rho^(n+1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (by positivity) (a_pos (by omega)).le)
      (pow_nonneg rho_pos.le _))
    (fun n => mul_le_mul_of_nonneg_right ?_ (pow_nonneg rho_pos.le _))
    (summable_index_geometric rho_pos.le rho_lt_one 2)
  have h := mul_le_mul_of_nonneg_left (a_le_index (j := n+1) (by omega))
    (show (0 : ℝ) ≤ n+1 by positivity)
  simpa [pow_two] using h

lemma gamma_pos : 0 < gamma := by
  apply inv_pos.mpr
  apply summable_moment.tsum_pos (i := 0)
  · intro n
    exact mul_nonneg (mul_nonneg (by positivity) (a_pos (by omega)).le)
      (pow_nonneg rho_pos.le _)
  · simpa using mul_pos (a_pos (j := 1) le_rfl) rho_pos

lemma alpha_pos (s : ℝ) : 0 < alpha s := mul_pos lam_pos (Real.exp_pos _)

end TotientAsymptotic

end

end OAI
