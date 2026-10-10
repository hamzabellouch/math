import OAI.Probability.SATComputability.CertificateSearch

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology
open RapidForcing.EffectiveArithmetic

theorem tolerance_tendsto :
    Tendsto (fun r => (tolerance r : ℝ)) atTop (nhds 0) := by
  simpa only [tolerance, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, inv_pow] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1))

structure TrialEvaluation where
  density : ℕ → ℚ
  valid : ℕ → Bool
  value : ℕ → ℝ
  approximate : ℕ × ℕ → ℚ
  density_computable : Computable density
  valid_computable : Computable valid
  approximate_computable : Computable approximate
  density_positive : ∀ j, valid j = true → 0 < density j
  approximation_error : ∀ j s, valid j = true →
    |(approximate (j, s) : ℝ) - value j| ≤ (tolerance s : ℝ)

def TrialEvaluation.certified (T : TrialEvaluation) (n : ℕ) : Bool :=
  decide (T.valid n.unpair.1 = true ∧
    T.approximate (n.unpair.1, n.unpair.2) + tolerance n.unpair.2 < 0)

def TrialEvaluation.upper (T : TrialEvaluation) (n : ℕ) : ℚ :=
  T.density n.unpair.1

theorem TrialEvaluation.certified_computable (T : TrialEvaluation) :
    Computable T.certified := by
  have := T.valid_computable
  have := T.approximate_computable
  unfold TrialEvaluation.certified
  fun_prop

theorem TrialEvaluation.upper_computable (T : TrialEvaluation) :
    Computable T.upper := by
  have := T.density_computable
  unfold TrialEvaluation.upper
  fun_prop

theorem TrialEvaluation.certified_negative (T : TrialEvaluation) {n : ℕ}
    (hn : T.certified n = true) :
    T.valid n.unpair.1 = true ∧ T.value n.unpair.1 < 0 := by
  have h : T.valid n.unpair.1 = true ∧
      T.approximate (n.unpair.1, n.unpair.2) + tolerance n.unpair.2 < 0 := by
    simpa only [TrialEvaluation.certified, decide_eq_true_eq] using hn
  refine ⟨h.1, ?_⟩
  have he := (abs_le.mp (T.approximation_error n.unpair.1 n.unpair.2 h.1)).1
  have hn' : (T.approximate (n.unpair.1, n.unpair.2) : ℝ) +
      (tolerance n.unpair.2 : ℝ) < 0 := by exact_mod_cast h.2
  linarith

theorem TrialEvaluation.negative_eventually_certified (T : TrialEvaluation) {j : ℕ}
    (hj : T.valid j = true) (hneg : T.value j < 0) :
    ∃ s, T.certified (Nat.pair j s) = true := by
  have hsmall := tolerance_tendsto.eventually_lt_const
    (show (0 : ℝ) < -T.value j / 2 by linarith)
  obtain ⟨s, hs⟩ := hsmall.exists
  have he := (abs_le.mp (T.approximation_error j s hj)).2
  have h : T.approximate (j, s) + tolerance s < 0 := by
    have : (T.approximate (j, s) : ℝ) + (tolerance s : ℝ) < 0 := by linarith
    exact_mod_cast this
  exact ⟨s, by simp [TrialEvaluation.certified, hj, h]⟩

structure TrialSeparation (T : TrialEvaluation) (α : ℝ) : Prop where
  sound : ∀ j, T.valid j = true → T.value j < 0 → α ≤ (T.density j : ℝ)
  complete : ∀ a : ℚ, α < (a : ℝ) →
    ∃ j, T.valid j = true ∧ T.density j = a ∧ T.value j < 0

theorem TrialSeparation.upper_sound {T : TrialEvaluation} {α : ℝ}
    (h : TrialSeparation T α) (n : ℕ) (hn : T.certified n = true) :
    α ≤ (T.upper n : ℝ) := by
  obtain ⟨hv, hg⟩ := T.certified_negative hn
  exact h.sound _ hv hg

theorem TrialSeparation.upper_dense {T : TrialEvaluation} {α : ℝ}
    (h : TrialSeparation T α) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, T.certified n = true ∧ (T.upper n : ℝ) < α + ε := by
  obtain ⟨a, ha, ha'⟩ := exists_rat_btwn (show α < α + ε by linarith)
  obtain ⟨j, hj, hd, hn⟩ := h.complete a ha
  obtain ⟨s, hs⟩ := T.negative_eventually_certified hj hn
  exact ⟨Nat.pair j s, hs, by simpa [TrialEvaluation.upper, hd] using ha'⟩

theorem trial_separation_of_pressure {T : TrialEvaluation} {α : ℝ}
    (hα : 0 ≤ α)
    (penalty : ℕ → ℕ) (pressure : ℚ → ℕ → ℝ)
    (hbelow : ∀ (a : ℚ) (b : ℕ), 0 < a → (a : ℝ) < α → 0 < b → 0 ≤ pressure a b)
    (habove : ∀ a : ℚ, α < (a : ℝ) → ∃ b, 0 < b ∧ pressure a b < 0)
    (hpositive : ∀ j, T.valid j = true → 0 < penalty j)
    (hbound : ∀ j, T.valid j = true → pressure (T.density j) (penalty j) ≤ T.value j)
    (hfinite : ∀ (a : ℚ) (b : ℕ), 0 < a → 0 < b → ∀ ε : ℝ, 0 < ε →
      ∃ j, T.valid j = true ∧ T.density j = a ∧ penalty j = b ∧
        T.value j < pressure a b + ε) :
    TrialSeparation T α := by
  constructor
  · intro j hj hneg
    by_contra h
    have hn := hbelow (T.density j) (penalty j) (T.density_positive j hj)
      (lt_of_not_ge h) (hpositive j hj)
    have hb := hbound j hj
    linarith
  · intro a ha
    obtain ⟨b, hb, hneg⟩ := habove a ha
    have ha' : 0 < a := by exact_mod_cast hα.trans_lt ha
    obtain ⟨j, hj, hd, _, hg⟩ := hfinite a b ha' hb (-pressure a b / 2) (by linarith)
    exact ⟨j, hj, hd, by linarith⟩

theorem computable_of_trial_separation {T : TrialEvaluation} {α : ℝ}
    (h : TrialSeparation T α) {lower : ℕ → ℚ} (hl : Computable lower)
    (hls : ∀ i, (lower i : ℝ) ≤ α)
    (hld : ∀ ε : ℝ, 0 < ε → ∃ i, α - ε < (lower i : ℝ)) :
    ∃ q : ℕ → ℚ, Computable q ∧
      ∀ r, |(q r : ℝ) - α| ≤ (2 ^ r : ℝ)⁻¹ := by
  obtain ⟨q, hq, _, he⟩ := finite_certificate_search hl T.upper_computable
    T.certified_computable hls h.upper_sound hld h.upper_dense
  exact ⟨q, hq, he⟩

end FixedClauseThreshold.Computability

end OAI
