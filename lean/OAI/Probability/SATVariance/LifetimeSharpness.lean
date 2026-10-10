import OAI.Probability.SATVariance.SharpnessEstimates

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma lifetime_parameters {k N : ℕ} (hN : 2 ≤ N) :
    N^(2*k) ≤ N^(2*k+1) ∧ k ≤ N^(2*k) ∧ 0 < N^(2*k+1) := by
  refine ⟨Nat.pow_le_pow_right (by omega) (by omega), ?_, by positivity⟩
  exact (Nat.le_of_lt Nat.lt_two_pow_self).trans
    ((Nat.pow_le_pow_left hN k).trans (Nat.pow_le_pow_right (by omega) (by omega)))

lemma lifetime_subcube_eventually (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^k / 2 ≤
      lifetime (N^(2*k+1)) k (subcube (N^(2*k+1)) (N^(2*k))) := by
  have hh := (killRatio_limit (by omega : 0 < 2*k) k).add
    (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ)^2))
  simp only [add_zero] at hh
  have hC : ((2 : ℝ)^k)⁻¹ < (1/2 : ℝ) := by
    have h8 : (8 : ℝ) ≤ 2^k := by
      have hh8 := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hk
      norm_num at hh8 ⊢
      exact hh8
    rw [← one_div]
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  filter_upwards [eventually_ge_atTop 2, hh.eventually_lt_const hC] with N hN hsmall
  obtain ⟨hbu, hkb, hu⟩ := lifetime_parameters (k := k) hN
  have hbound := subcube_block_upper hu hbu (hkb.trans hbu) (N^k)
  have he : (N^k : ℕ) * killRatio (N^(2*k+1)) (N^(2*k)) k +
      ((N^k : ℕ) : ℝ)^2 * (k : ℝ)^2 / (N^(2*k+1) : ℕ) =
      (N : ℝ)^k * killRatio (N^(2*k+1)) (N^(2*k)) k + (k : ℝ)^2/N := by
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    push_cast
    rw [pow_succ, pow_mul]
    field_simp
    ring
  rw [he] at hbound
  have hhalf : (1/2 : ℝ) ≤ 1 - blockKill (N^(2*k+1)) k (subcube (N^(2*k+1)) (N^(2*k))) (N^k) := by
    linarith
  have ht := lifetime_ge_survival (hkb.trans hbu) (subcube (N^(2*k+1)) (N^(2*k))) (N^k)
  push_cast at ht
  calc
    _ = (N : ℝ)^k * (1/2) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hhalf (pow_nonneg (Nat.cast_nonneg N) k)).trans ht

lemma killing_above_scale {m r : ℕ} (hm : 0 < m) (hr : 0 < r) :
    Tendsto (fun N : ℕ => killRatio (N^(m+1)) (N^m) r * ((N^(m+1) : ℕ) : ℝ)^r)
      atTop atTop := by
  have hh := (tendsto_nat_pow_real (m*r) (by positivity)).atTop_mul_pos
    (by positivity : (0 : ℝ) < ((2 : ℝ)^r)⁻¹) (killRatio_limit hm r)
  apply hh.congr'
  filter_upwards [] with N
  push_cast
  calc
    _ = (N : ℝ)^(m*r+r) * killRatio (N^(m+1)) (N^m) r := by rw [pow_add]; ring
    _ = _ := by rw [show m*r+r = (m+1)*r by ring, pow_mul]; ring

lemma rpow_rescaling {x q : ℝ} (hx : 0 < x) (hq : 0 ≤ q) (k r : ℕ) (γ : ℝ) :
    x^((k : ℝ) - (r : ℝ)*γ) * (x^r*q)^γ = x^k * q^γ := by
  rw [Real.mul_rpow (pow_nonneg hx.le _) hq, ← Real.rpow_natCast_mul hx.le,
    ← mul_assoc, ← Real.rpow_add hx]
  simp only [sub_add_cancel, Real.rpow_natCast]

lemma lifetime_ratio_growth (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ < (k : ℝ)/((k-1 : ℕ) : ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)^k / 2 * (killRatio (N^(2*k+1)) (N^(2*k)) (k-1))^γ)
      atTop atTop := by
  have hr : (0 : ℝ) < ((k-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k-1)
  have hδ : 0 < (k : ℝ) - ((k-1 : ℕ) : ℝ)*γ := by
    have h := (lt_div_iff₀ hr).mp hγ
    nlinarith
  have hh := (killRatio_limit (by omega : 0 < 2*k) (k-1)).rpow_const (p := γ) (Or.inl (by positivity))
  have hp := ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).atTop_mul_pos
    (Real.rpow_pos_of_pos (by positivity) γ) hh
  have hp' := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1/2) hp
  apply hp'.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  simp only [Function.comp_apply]
  rw [rpow_rescaling (by positivity : (0 : ℝ) < N) (killRatio_nonneg _ _ _) k (k-1) γ]
  ring

theorem lifetime_sharp (k : ℕ) (hk : 3 ≤ k) (γ D A : ℝ)
    (hγ : γ < (k : ℝ) / ((k-1 : ℕ) : ℝ)) (_hD : 0 < D) (_hA : 0 < A) :
    ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ k ≤ u ∧ ∃ S : Finset (Assignment u),
      S.Nonempty ∧ A * (u : ℝ) ^ (-((k-1 : ℕ) : ℝ)) ≤ blockKill u (k-1) S 1 ∧
      D * (blockKill u (k-1) S 1) ^ (-γ) < lifetime u k S := by
  intro M
  have ha := (killing_above_scale (by omega : 0 < 2*k) (by omega : 0 < k-1)).eventually_gt_atTop A
  have hd := (lifetime_ratio_growth k hk γ hγ).eventually_gt_atTop D
  obtain ⟨N, hN, hMN, ha, hd, ht⟩ :=
    ((eventually_ge_atTop 2).and ((eventually_ge_atTop M).and
      (ha.and (hd.and (lifetime_subcube_eventually k hk))))).exists
  obtain ⟨hbu, hkb, hu⟩ := lifetime_parameters (k := k) hN
  have hku := hkb.trans hbu
  have hru : k-1 ≤ N^(2*k+1) := by omega
  refine ⟨N^(2*k+1), hMN.trans (Nat.le_pow (by omega)), hku,
    subcube (N^(2*k+1)) (N^(2*k)), subcube_nonempty _ _, ?_, ?_⟩
  · rw [subcube_one hbu hru, Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity)).mpr ha.le
  · rw [subcube_one hbu hru]
    have hq : 0 < killRatio (N^(2*k+1)) (N^(2*k)) (k-1) := killRatio_pos (by omega) hru
    rw [Real.rpow_neg hq.le, ← div_eq_mul_inv]
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hq γ)).mpr hd).trans_le ht

end RandomKSAT

end

end OAI
