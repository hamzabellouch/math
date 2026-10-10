import OAI.Analysis.KadisonKastler.ConstructedFiniteFactorStability
import OAI.Analysis.KadisonKastler.FiniteFactorModulus

namespace OAI

/-! # A uniform tolerance for the finite-factor displacement estimate -/

namespace KadisonKastler

open Filter Topology

noncomputable section

theorem continuous_constructedFiniteFactorError : Continuous constructedFiniteFactorError := by
  unfold constructedFiniteFactorError
  exact (continuous_const.mul continuous_id).add
    (continuous_const.mul (continuous_commonPositionError.comp
      (continuous_const.mul continuous_id)))

@[simp] theorem constructedFiniteFactorError_zero : constructedFiniteFactorError 0 = 0 := by
  simp [constructedFiniteFactorError]

theorem constructedFiniteFactorError_monotone : Monotone constructedFiniteFactorError := by
  intro a b hab
  unfold constructedFiniteFactorError
  exact add_le_add (mul_le_mul_of_nonneg_left hab (by norm_num))
    (mul_le_mul_of_nonneg_left (commonPositionError_monotone
      (mul_le_mul_of_nonneg_left hab (by norm_num))) (by norm_num))

/-- All smallness requirements hold at one positive tolerance, uniformly
in the factors and the Hilbert space. -/
theorem exists_constructed_finiteFactor_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 / 100 ∧
      302 * t < 174 / 1000000000000000 ∧
      3 * 50948 * Real.sqrt (302 * t) < 1 / 100000 ∧
      commonPositionError (302 * t) < 1 / 4000000 ∧ constructedFiniteFactorError t < ε := by
  have ht : ∀ᶠ t : ℝ in 𝓝 0, t < 1 / 100 :=
    continuousAt_id.eventually_lt_const (by norm_num)
  have hp : ∀ᶠ t : ℝ in 𝓝 0, 302 * t < 174 / 1000000000000000 :=
    (continuous_const.mul continuous_id).continuousAt.eventually_lt_const (by norm_num)
  have hs : Continuous (fun t : ℝ => 3 * 50948 * Real.sqrt (302 * t)) := by fun_prop
  have hs' : ∀ᶠ t : ℝ in 𝓝 0, 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000 :=
    hs.continuousAt.eventually_lt_const (by norm_num)
  have hc : Continuous (fun t : ℝ => commonPositionError (302 * t)) :=
    continuous_commonPositionError.comp (continuous_const.mul continuous_id)
  have hc' : ∀ᶠ t : ℝ in 𝓝 0, commonPositionError (302 * t) < 1 / 4000000 :=
    hc.continuousAt.eventually_lt_const (by norm_num)
  have he : ∀ᶠ t : ℝ in 𝓝 0, constructedFiniteFactorError t < ε :=
    continuous_constructedFiniteFactorError.continuousAt.eventually_lt_const (by simpa using hε)
  have hall : ∀ᶠ t : ℝ in 𝓝 0, t < 1 / 100 ∧
      302 * t < 174 / 1000000000000000 ∧
      3 * 50948 * Real.sqrt (302 * t) < 1 / 100000 ∧
      commonPositionError (302 * t) < 1 / 4000000 ∧ constructedFiniteFactorError t < ε := by
    filter_upwards [ht, hp, hs', hc', he] with t h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  obtain ⟨d, hd, hall⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨d / 2, half_pos hd, hall ?_⟩
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hd)] using
    (half_lt_self hd)

end

end KadisonKastler

end OAI
