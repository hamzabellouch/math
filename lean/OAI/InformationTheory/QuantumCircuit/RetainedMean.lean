import OAI.InformationTheory.QuantumCircuit.HeavyOutcome

namespace OAI

/-! Mean excitation counts of retained reflection layers. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

lemma eventually_exp_le_negative_power {p : ℝ} (hp : 0 < p) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-((N : ℝ)^p)) ≤ (N : ℝ)^(-c) := by
  filter_upwards [eventually_power_log_le hp c, eventually_ge_atTop 1] with N hc hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  conv_rhs => rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  simp only [Real.rpow_zero, mul_one] at hc
  nlinarith only [hc]

theorem retained_test_mean
    (hspec : PublishedProductSpectralResolution) (d : ℕ)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (P : ∀ ν, ProductInput (m ν))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ U : Operator (m ν), IsCircuit d U → ∀ B : Count (m ν),
      (m ν : ℝ)^(-6 : ℝ) ≤ ‖act B.zero (act U (P ν).state)‖^2 →
      meanCount B (act U (P ν).state) ≤ (m ν : ℝ)^ε := by
  have hp : 0 < ε / 4 := by positivity
  have hph : ε / 4 < ε / 2 := by linarith
  filter_upwards [uniform_product_overlap_tail d m hm P hp hph,
    hm.eventually (eventually_exp_le_negative_power hp 7),
    hm.eventually (eventually_two_powers_le (show ε / 2 < ε by linarith) hε),
    hm.eventually (eventually_ge_atTop 1)] with ν hov hex hsum hN
  intro U hU B hret
  let ψ := act U (P ν).state
  let T := ‖act (B.high ((m ν : ℝ)^(ε / 2))) ψ‖
  have hn : (0 : ℝ) < m ν := by exact_mod_cast (show 0 < m ν by omega)
  have hn1 : (1 : ℝ) ≤ m ν := by exact_mod_cast hN
  have hT : T ≤ (m ν : ℝ)^(-1 : ℝ) := by
    have hmul : (m ν : ℝ)^(-6 : ℝ) * T ≤ (m ν : ℝ)^(-7 : ℝ) :=
      (mul_le_mul_of_nonneg_right hret (norm_nonneg _)).trans ((hov U hU B).trans hex)
    have hdiv : T ≤ (m ν : ℝ)^(-7 : ℝ) / (m ν : ℝ)^(-6 : ℝ) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hn _)).mpr (by simpa only [mul_comm] using hmul)
    rw [← Real.rpow_sub hn] at hdiv
    norm_num at hdiv
    exact hdiv
  have hT1 : T ≤ 1 := hT.trans (by rw [Real.rpow_neg_one]; exact inv_le_one_of_one_le₀ hn1)
  have hnT : (m ν : ℝ) * T ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hT hn.le
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hn.ne'] at hh
    exact hh
  have htiny : (m ν : ℝ) * T^2 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hnT (norm_nonneg (act (B.high ((m ν : ℝ)^(ε / 2))) ψ))]
  have hψ : ‖ψ‖ = 1 := (act_unitary_norm hU.mem_unitary _).trans (P ν).norm_state
  have hh := meanCount_le_cut hspec B ψ (r := (m ν : ℝ)^(ε / 2)) (by positivity)
  rw [hψ, one_pow, mul_one] at hh
  simp only [Real.rpow_zero] at hsum
  dsimp [T] at htiny
  linarith only [hh, htiny, hsum]

end QAC

end

end OAI
