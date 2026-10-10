import OAI.Probability.SATVariance.Subcube

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma lifetime_ge_survival {u k : ℕ} (hku : k ≤ u) (S : Finset (Assignment u)) (t : ℕ) :
    (t : ℝ) * (1 - blockKill u k S t) ≤ lifetime u k S := by
  let := streamLaw_probability u k hku
  have he : 1 - blockKill u k S t = survival u k S t := by
    rw [blockKill_compl hku, survival_eq_prob hku]
    ring
  have hm (m : ℕ) (hmt : m ≤ t) : survival u k S t ≤ survival u k S m := by
    rw [survival_eq_prob hku, survival_eq_prob hku]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    rintro ω ⟨a, ha, hcs⟩
    exact ⟨a, ha, fun i hi => hcs i (hi.trans_le hmt)⟩
  rw [he, lifetime]
  calc
    _ = ∑ _m ∈ Finset.range t, survival u k S t := by simp
    _ ≤ ∑ m ∈ Finset.range t, survival u k S m :=
      Finset.sum_le_sum fun m hm' => hm m (Finset.mem_range.mp hm').le
    _ ≤ ∑' m, survival u k S m :=
      (survival_summable hku S).sum_le_tsum (Finset.range t) (fun m _ => survival_nonneg u k S m)

lemma tendsto_nat_pow_real (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N : ℕ => (N : ℝ)^m) atTop atTop :=
  (tendsto_pow_atTop (Nat.ne_of_gt hm)).comp tendsto_natCast_atTop_atTop

lemma subcube_factor_limit {m : ℕ} (hm : 0 < m) (s : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * ((N^m : ℕ) - (s : ℝ)) /
      (2 * ((N^(m+1) : ℕ) - (s : ℝ)))) atTop (𝓝 (1/2 : ℝ)) := by
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) - s/(N : ℝ)^m) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds (x := (s : ℝ))).div_atTop (tendsto_nat_pow_real m hm))
  have h2 : Tendsto (fun N : ℕ => (2 : ℝ) * (1 - s/(N : ℝ)^(m+1))) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (s : ℝ))).div_atTop (tendsto_nat_pow_real (m+1) (by omega))))
  apply (h1.div h2 (by norm_num)).congr'
  filter_upwards [eventually_ge_atTop (s+1)] with N hN
  have hN0 : 0 < N := by omega
  have hx : (N : ℝ) ≠ 0 := by positivity
  have hsN : s < N^(m+1) := lt_of_lt_of_le (by omega) (Nat.le_pow (by omega))
  have hden : (N : ℝ)^(m+1) - s ≠ 0 := by
    have hh : (s : ℝ) < (N^(m+1) : ℕ) := by exact_mod_cast hsN
    push_cast at hh
    linarith
  change (1 - (s : ℝ)/(N : ℝ)^m) / (2 * (1 - (s : ℝ)/(N : ℝ)^(m+1))) = _
  push_cast
  field_simp
  ring

lemma killRatio_limit {m : ℕ} (hm : 0 < m) (s : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ)^s * killRatio (N^(m+1)) (N^m) s)
      atTop (𝓝 (((2 : ℝ)^s)⁻¹)) := by
  induction s with
  | zero => simp [killRatio_zero]
  | succ s ih =>
    have hh := ih.mul (subcube_factor_limit hm s)
    have hc : ((2 : ℝ)^s)⁻¹ * (1/2) = ((2 : ℝ)^(s+1))⁻¹ := by
      rw [pow_succ, mul_inv_rev]
      ring
    rw [hc] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (s+1)] with N hN
    have hsb : s ≤ N^m := (by omega : s ≤ N).trans (Nat.le_pow hm)
    have hsu : s < N^(m+1) := lt_of_lt_of_le (by omega) (Nat.le_pow (by omega))
    rw [killRatio_succ hsu hsb, pow_succ]
    ring

end RandomKSAT

end

end OAI
