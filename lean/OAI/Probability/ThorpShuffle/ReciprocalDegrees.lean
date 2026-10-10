import OAI.Probability.ThorpShuffle.DegreeBounds

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open Filter Topology

namespace Thorp.Analysis

lemma sqrt_log_small (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n + 1) ≤ c * Real.sqrt (n + 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero.comp ht
  have he := h.eventually (gt_mem_nhds hc)
  filter_upwards [he] with n hn
  dsimp only [Function.comp_apply] at hn
  rw [← Real.sqrt_eq_rpow] at hn
  exact ((div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity))).mp hn).le

lemma partition_exponential_decay :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * Nat.sqrt n) / (4 : ℝ) ^ (n / 16)) atTop (𝓝 0) := by
  have hc : 0 < Real.log 4 / 256 := by positivity
  have he := sqrt_log_small (Real.log 4 / 256) hc
  have ht : Tendsto (fun n : ℕ => Real.exp (-(Real.log 4 / 64) * n)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos (by positivity))
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ ht
  filter_upwards [he, eventually_ge_atTop 32] with n hn hn32
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n + 1) := by
    apply Real.le_sqrt_of_sq_le
    have hh : ((Nat.sqrt n : ℝ)^2) ≤ n := by exact_mod_cast (show (Nat.sqrt n)^2 ≤ n by simpa only [pow_two] using Nat.sqrt_le n)
    linarith
  have hdiv : (n : ℝ) / 32 ≤ (n / 16 : ℕ) := by
    have hh : n ≤ 32 * (n / 16) := by omega
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr (by exact_mod_cast (by omega : n ≤ n / 16 * 32))
  have hp : 2 * (Nat.sqrt n : ℝ) * Real.log (n + 1) ≤ (Real.log 4 / 64) * n := by
    have hl : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
    have h₁ := mul_le_mul_of_nonneg_right hs hl
    have h₂ := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg ((n : ℝ) + 1))
    have hh := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    have hc0 : 0 ≤ Real.log 4 / 256 := hc.le
    have hsq : Real.sqrt (n + 1) * ((Real.log 4 / 256) * Real.sqrt (n + 1)) = (Real.log 4 / 256) * (n + 1) := by calc
      _ = (Real.log 4 / 256) * (Real.sqrt (n + 1))^2 := by ring
      _ = _ := by rw [hh]
    rw [hsq] at h₂
    have h₃ := mul_le_mul_of_nonneg_left (show (n : ℝ) + 1 ≤ 2 * n by linarith) hc0
    linarith only [h₁, h₂, h₃]
  have hq : -(Real.log 4 / 64) * n ≥
      (2 * Nat.sqrt n : ℕ) * Real.log (n + 1) - (n / 16 : ℕ) * Real.log 4 := by
    push_cast
    have hh := mul_le_mul_of_nonneg_right hdiv (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    linarith
  calc
    _ = Real.exp ((2 * Nat.sqrt n : ℕ) * Real.log (n + 1) - (n / 16 : ℕ) * Real.log 4) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by positivity), Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ ≤ _ := Real.exp_le_exp.mpr hq

end Thorp.Analysis

namespace Thorp.Specht
open scoped Classical
open Filter Topology Thorp.Young

variable {n : ℕ}

def inverseDegree (p : NShape n) : ℝ := ((degree p : ℝ)^2)⁻¹

def slice (n u : ℕ) : ℝ := ∑ p : {p : NShape n // defect p = u}, inverseDegree p.val

def smallSlice (n u : ℕ) : ℝ := if 0 < u ∧ 4 * u ≤ n then slice n u else 0

def exceptionalReciprocalSum (n : ℕ) : ℝ := ∑ p : NShape n, if 0 < defect p then inverseDegree p else 0

lemma inverseDegree_nonneg (p : NShape n) : 0 ≤ inverseDegree p := by unfold inverseDegree; positivity
lemma slice_nonneg (n u : ℕ) : 0 ≤ slice n u := Finset.sum_nonneg (fun _ _ => inverseDegree_nonneg _)
lemma smallSlice_nonneg (n u : ℕ) : 0 ≤ smallSlice n u := by unfold smallSlice; split_ifs; exact slice_nonneg _ _; rfl

lemma slice_bound (n u : ℕ) (K : ℝ) (hK : 0 < K)
    (hk : ∀ p : NShape n, defect p = u → K ≤ degree p) :
    slice n u ≤ (2 : ℝ)^(u+1) / K^2 := by
  have hI (p : {p : NShape n // defect p = u}) : inverseDegree p.val ≤ (K^2)⁻¹ := by
    apply inv_anti₀ (pow_pos hK 2)
    exact pow_le_pow_left₀ hK.le (hk p.val p.property) 2
  calc
    _ ≤ ∑ _ : {p : NShape n // defect p = u}, (K^2)⁻¹ := Finset.sum_le_sum (fun p _ => hI p)
    _ = (Fintype.card {p : NShape n // defect p = u} : ℝ) * (K^2)⁻¹ := by simp
    _ ≤ (2 : ℝ)^(u+1) * (K^2)⁻¹ := mul_le_mul_of_nonneg_right (by exact_mod_cast defect_card_bound n u) (by positivity)
    _ = _ := rfl

lemma smallSlice_bound (n u : ℕ) : smallSlice n u ≤ 2 * (2 / 9 : ℝ)^u := by
  unfold smallSlice
  split_ifs with h
  · have hk : ∀ p : NShape n, defect p = u → (3 : ℝ)^u ≤ degree p := by
      intro p hp
      have hh := small_defect_degree p (by rw [hp]; exact h.2)
      rw [hp] at hh
      exact_mod_cast hh
    have hh := slice_bound n u (3^u) (by positivity) hk
    have he : (2 : ℝ)^(u+1) / (3^u)^2 = 2 * (2/9 :ℝ)^u := by
      rw [pow_succ, div_pow]
      have hp : ((3 : ℝ)^u) ^ 2 = 9^u := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      rw [hp]
      ring
    exact hh.trans_eq he
  · positivity

lemma smallSlice_tendsto (u : ℕ) : Tendsto (fun n => smallSlice n u) atTop (𝓝 0) := by
  by_cases hu : 0 < u
  · have ht : Tendsto (fun n : ℕ => ((n - 2*u + 1 : ℕ) : ℝ)) atTop atTop := by
      exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        ((tendsto_add_atTop_nat 1).comp (tendsto_sub_atTop_nat (2*u)))
    have hi : Tendsto (fun n : ℕ => (((n - 2*u + 1 : ℕ) : ℝ)^2)⁻¹) atTop (𝓝 0) := by
      apply tendsto_inv_atTop_zero.comp
      simpa only [pow_two] using ht.atTop_mul_atTop₀ ht
    have he := hi.const_mul ((2 : ℝ)^(u+1))
    rw [mul_zero] at he
    apply squeeze_zero' (Eventually.of_forall (fun n => smallSlice_nonneg n u)) _ he
    filter_upwards [eventually_ge_atTop (4*u)] with n hn
    rw [smallSlice, ite_eq_left ⟨hu, hn⟩]
    exact slice_bound n u _ (by positivity) (fun p hp => by
      have hh := fixed_defect_degree p (by rwa [hp]) (by rw [hp]; omega)
      rw [hp] at hh
      exact_mod_cast hh)
  · simp only [smallSlice, hu, false_and, ↓reduceIte]
    exact tendsto_const_nhds

lemma smallSum_tendsto : Tendsto (fun n => ∑' u, smallSlice n u) atTop (𝓝 0) := by
  have hs : Summable (fun u : ℕ => 2 * (2/9 : ℝ)^u) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(2/9 : ℝ)‖ < 1)).mul_left 2
  have h := tendsto_tsum_of_dominated_convergence hs smallSlice_tendsto
    (Eventually.of_forall (fun n u => by rw [Real.norm_of_nonneg (smallSlice_nonneg n u)]; exact smallSlice_bound n u))
  simpa only [tsum_zero] using h

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical
open Filter Topology Thorp.Young

lemma smallSlice_as_sum (n u : ℕ) :
    smallSlice n u = ∑ p : NShape n,
      if defect p = u ∧ 0 < defect p ∧ 4 * defect p ≤ n then inverseDegree p else 0 := by
  unfold smallSlice slice
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : NShape n => defect p = u)) (by simp), Finset.sum_filter]
  by_cases h : 0 < u ∧ 4 * u ≤ n
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : defect p = u
    · simp only [hp, h.1, h.2, true_and, ↓reduceIte]
    · simp only [hp, false_and, ↓reduceIte]
  · rw [ite_eq_right h]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with hp
    · exact (h (by simpa only [hp.1] using hp.2)).elim
    · rfl

lemma smallSlice_support (n u : ℕ) (hu : u ∉ Finset.range (n+1)) : smallSlice n u = 0 := by
  unfold smallSlice
  have hh : ¬(0 < u ∧ 4*u ≤ n) := by have := (Finset.mem_range.not.mp hu); omega
  exact ite_eq_right hh

lemma smallSum_eq (n : ℕ) :
    (∑' u, smallSlice n u) = ∑ p : NShape n,
      if 0 < defect p ∧ 4 * defect p ≤ n then inverseDegree p else 0 := by
  rw [tsum_eq_sum (smallSlice_support n)]
  simp_rw [smallSlice_as_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hd : defect p ∈ Finset.range (n+1) := Finset.mem_range.mpr (by have := defect_add_longest p; omega)
  have he (u : ℕ) : (if defect p = u ∧ 0 < defect p ∧ 4 * defect p ≤ n then inverseDegree p else 0) =
      if defect p = u then (if 0 < defect p ∧ 4 * defect p ≤ n then inverseDegree p else 0) else 0 := by
    split_ifs <;> tauto
  simp only [he, Finset.sum_ite_eq, hd, ↓reduceIte]

lemma bulkSum_bound (n : ℕ) (hn : 0 < n) :
    (∑ p : NShape n, if n < 4 * defect p then inverseDegree p else 0) ≤
      ((n : ℝ)+1)^(2*Nat.sqrt n) / (4:ℝ)^(n/16) := by
  have hb (p : NShape n) : (if n < 4*defect p then inverseDegree p else 0) ≤ ((4:ℝ)^(n/16))⁻¹ := by
    by_cases hp : n < 4*defect p
    · rw [ite_eq_left hp]
      have hh := bulk_degree p hn hp
      have he : ((2 : ℝ)^(n/16))^2 = (4:ℝ)^(n/16) := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      apply inv_anti₀ (by positivity)
      change (4:ℝ)^(n/16) ≤ (degree p : ℝ)^2
      rw [← he]
      exact pow_le_pow_left₀ (by positivity) hh 2
    · rw [ite_eq_right hp]; positivity
  have hc : Fintype.card (NShape n) ≤ (n+1)^(2*Nat.sqrt n) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (Nat.Partition (Fintype.card (Fin n))) ≤ _
    rw [Fintype.card_fin, ← Fintype.card_eq_nat_card]
    exact partition_count_le_sqrt_pow n
  calc
    _ ≤ ∑ _ : NShape n, ((4:ℝ)^(n/16))⁻¹ := Finset.sum_le_sum (fun p _ => hb p)
    _ = (Fintype.card (NShape n) : ℝ) * ((4:ℝ)^(n/16))⁻¹ := by simp
    _ ≤ ((n:ℝ)+1)^(2*Nat.sqrt n) * ((4:ℝ)^(n/16))⁻¹ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := rfl

lemma exceptionalReciprocalSum_split (n : ℕ) : exceptionalReciprocalSum n =
    (∑' u, smallSlice n u) + (∑ p : NShape n, if n < 4 * defect p then inverseDegree p else 0) := by
  rw [smallSum_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp_all
  all_goals omega

theorem exceptionalReciprocalSum_tendsto : Tendsto exceptionalReciprocalSum atTop (𝓝 0) := by
  have hb : Tendsto (fun n => ∑ p : NShape n, if n < 4 * defect p then inverseDegree p else 0) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => Finset.sum_nonneg (fun p _ => by split_ifs; exact inverseDegree_nonneg p; rfl)))
      ((eventually_gt_atTop 0).mono (fun n hn => bulkSum_bound n hn)) Thorp.Analysis.partition_exponential_decay
  have he : exceptionalReciprocalSum = (fun n => (∑' u, smallSlice n u) + ∑ p : NShape n, if n < 4 * defect p then inverseDegree p else 0) := funext exceptionalReciprocalSum_split
  rw [he]
  simpa only [zero_add] using smallSum_tendsto.add hb

end Thorp.Specht

end

end OAI
