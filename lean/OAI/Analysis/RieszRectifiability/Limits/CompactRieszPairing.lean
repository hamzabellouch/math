import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.OuterPairingLimit

namespace OAI

/-!
# Compactly supported Lipschitz Riesz pairings

Growth bounds control the exterior pairing of a compactly supported Lipschitz test.
Finite ball restrictions then connect truncated pairings to the renormalized
pairing through the outer-radius limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszFarIntegrand_integrable_of_compact_lipschitz {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) := by
  let ν := μ.restrict (ball a R)
  let w := affineNormalHeight e a 0
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w ‖e‖₊ hw a R hR
  have hφL2 := lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR
  have hφI := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν := memLp_one_iff_integrable.mp (hφL2.mul hwL2)
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w ‖e‖₊ hw a R hR
  have hN := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable hφI hφw a H R hH hR hHR
    (Filter.Eventually.of_forall hsupport) hweighted _ hZ).1
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have heq : rieszFarIntegrand m e φ a = renormalizedNormalIntegrand m w φ a := by
    funext q
    rw [rieszFarIntegrand_eq_normal_sub_correction m e w φ (affineNormalHeight_difference e a 0),
      hwa, mul_zero, zero_mul, sub_zero]
  rw [heq]
  exact hN

theorem native_pairing_eq_finite_localization {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (φ : Ambient d → ℝ)
    (a : Ambient d) (R T ε : ℝ) (hRT : R ≤ T) (hφzero : ∀ x ∉ ball a R, φ x = 0) :
    (∫ x, φ x * inner ℝ e (truncated m (μ.restrict (ball a T)) ε (fun _ => 1) x) ∂μ.restrict (ball a T)) =
      ∫ x, φ x * inner ℝ e (truncated m μ ε ((ball a T).indicator (fun _ => 1)) x) ∂μ := by
  simp_rw [truncated_restriction_eq_indicator m μ (ball a T) measurableSet_ball]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : φ x = 0 := hφzero x (fun hin => hx ((ball_subset_ball hRT) hin))
  rw [hz, zero_mul]

theorem riesz_pairing_as_iterated_hard_limits {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (hzero : (∫ x in ball a R, φ x ∂μ) = 0) :
    (∀ k : ℕ, Tendsto (fun j : ℕ => ∫ x, φ x * inner ℝ e
      (truncated (p + 1) μ ((1 / 2 : ℝ) ^ j)
        ((ball a (outerPairRadius R k)).indicator (fun _ => 1)) x) ∂μ)
      atTop (𝓝 (rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius R k))) a R e φ))) ∧
    Tendsto (fun k : ℕ => rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius R k))) a R e φ)
      atTop (𝓝 (rieszScalarPairing (p + 1) μ a R e φ)) := by
  have hφzero : ∀ x ∉ ball a R, φ x = 0 := by
    intro x hx
    by_contra hn
    apply hx
    exact (hsupport x hn).trans_lt (by linarith : H < R)
  refine ⟨?_, rieszScalarPairing_outer_limit (p + 1) μ a R e φ
    (rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ a H R hH hR hHR hsupport)⟩
  intro k
  let T := outerPairRadius R k
  let ν := μ.restrict (ball a T)
  have hT : 0 < T := outerPairRadius_pos R hR k
  have hRT : R ≤ T := outerPairRadius_ge R k
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a T hT
  have hφI : Integrable φ ν := (lipschitz_height_memLp_on_ball (p + 1) C μ hg φ L hφ a T hT).integrable (by norm_num)
  have hzeroν : (∫ x in ball a R, φ x ∂ν) = 0 := by
    change (∫ x, φ x ∂(μ.restrict (ball a T)).restrict (ball a R)) = 0
    rw [restrict_ball_nested μ a R T hRT]
    exact hzero
  have ht := finite_truncations_tendsto_renormalized p C ν
    (globalGrowth_restrict (p + 1) C μ hg (ball a T)) e φ L hφ hφI
    (2 * T) (by positivity) (ball_restriction_pair_diameter μ a T) a R hR hφzero hzeroν
  have heq : (fun j : ℕ => ∫ x, φ x * inner ℝ e (truncated (p + 1) ν ((1 / 2 : ℝ) ^ j) (fun _ => 1) x) ∂ν) =
      fun j => ∫ x, φ x * inner ℝ e (truncated (p + 1) μ ((1 / 2 : ℝ) ^ j)
        ((ball a T).indicator (fun _ => 1)) x) ∂μ := by
    funext j
    exact native_pairing_eq_finite_localization (p + 1) μ e φ a R T _ hRT hφzero
  rw [heq] at ht
  exact ht

end

end RieszRectifiability

end OAI
