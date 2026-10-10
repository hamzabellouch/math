import OAI.Analysis.KadisonKastler.FiniteFactorStability

namespace OAI

/-! # A uniform tolerance for the finite-factor displacement estimate -/

namespace KadisonKastler

open Filter Topology

noncomputable section

theorem continuous_commonPositionError : Continuous commonPositionError := by
  unfold commonPositionError
  fun_prop

@[simp] theorem commonPositionError_zero : commonPositionError 0 = 0 := by
  simp [commonPositionError]

theorem continuous_finiteFactorError : Continuous finiteFactorError := by
  unfold finiteFactorError
  exact (continuous_const.mul continuous_id).add
    (continuous_const.mul (continuous_commonPositionError.comp
      (continuous_const.mul continuous_id)))

@[simp] theorem finiteFactorError_zero : finiteFactorError 0 = 0 := by
  simp [finiteFactorError]

theorem commonPositionError_monotone : Monotone commonPositionError := by
  intro a b hab
  unfold commonPositionError
  gcongr

theorem finiteFactorError_monotone : Monotone finiteFactorError := by
  intro a b hab
  unfold finiteFactorError
  exact add_le_add (mul_le_mul_of_nonneg_left hab (by norm_num))
    (mul_le_mul_of_nonneg_left (commonPositionError_monotone
      (mul_le_mul_of_nonneg_left hab (by norm_num))) (by norm_num))

/-- All smallness requirements hold at one positive tolerance, uniformly
in the factors and the Hilbert space. -/
theorem exists_finiteFactor_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 / 100 ∧
      302 * t < 174 / 1000000000000000 ∧
      3 * 50948 * Real.sqrt (302 * t) < 1 / 100000 ∧
      commonPositionError (302 * t) < 1 / 2400 ∧ finiteFactorError t < ε := by
  have ht : ∀ᶠ t : ℝ in 𝓝 0, t < 1 / 100 :=
    continuousAt_id.eventually_lt_const (by norm_num)
  have hp : ∀ᶠ t : ℝ in 𝓝 0, 302 * t < 174 / 1000000000000000 :=
    (continuous_const.mul continuous_id).continuousAt.eventually_lt_const (by norm_num)
  have hs : Continuous (fun t : ℝ => 3 * 50948 * Real.sqrt (302 * t)) := by fun_prop
  have hs' : ∀ᶠ t : ℝ in 𝓝 0, 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000 :=
    hs.continuousAt.eventually_lt_const (by norm_num)
  have hc : Continuous (fun t : ℝ => commonPositionError (302 * t)) :=
    continuous_commonPositionError.comp (continuous_const.mul continuous_id)
  have hc' : ∀ᶠ t : ℝ in 𝓝 0, commonPositionError (302 * t) < 1 / 2400 :=
    hc.continuousAt.eventually_lt_const (by norm_num)
  have he : ∀ᶠ t : ℝ in 𝓝 0, finiteFactorError t < ε :=
    continuous_finiteFactorError.continuousAt.eventually_lt_const (by simpa using hε)
  have hall : ∀ᶠ t : ℝ in 𝓝 0, t < 1 / 100 ∧
      302 * t < 174 / 1000000000000000 ∧
      3 * 50948 * Real.sqrt (302 * t) < 1 / 100000 ∧
      commonPositionError (302 * t) < 1 / 2400 ∧ finiteFactorError t < ε := by
    filter_upwards [ht, hp, hs', hc', he] with t h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  obtain ⟨d, hd, hall⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨d / 2, half_pos hd, hall ?_⟩
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hd)] using
    (half_lt_self hd)

end

end KadisonKastler

end OAI
