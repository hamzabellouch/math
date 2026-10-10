import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactRieszPairing

namespace OAI

/-!
# Fixed-cutoff limits of hard-truncated pairings

Restricting a globally growing measure to the outer ball gives a finite measure.
Mean-zero Lipschitz tests then identify the limit of dyadic hard truncations
with the scalar Riesz pairing on that restriction. The ball indicator also has
finite squared integral equal to the real mass of the ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem fixed_cutoff_hard_pairing_limit {d : ℕ} (p : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) G μ)
    (a : Ambient d) (T : ℝ) (hT : 0 < T)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (z : Ambient d) (R : ℝ) (hR : 0 < R)
    (houter : ∀ x ∉ ball a T, φ x = 0)
    (hinner : ∀ x ∉ ball z R, φ x = 0)
    (hzero : (∫ x, φ x ∂μ) = 0) :
    Tendsto (fun k : ℕ => ∫ x, φ x * inner ℝ e
      (truncated (p + 1) μ ((1 / 2 : ℝ) ^ k) ((ball a T).indicator (fun _ => 1)) x) ∂μ)
      atTop (𝓝 (rieszScalarPairing (p + 1) (μ.restrict (ball a T)) z R e φ)) := by
  let ν := μ.restrict (ball a T)
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) G μ hg a T hT
  have hφI : Integrable φ ν :=
    (lipschitz_height_memLp_on_ball (p + 1) G μ hg φ L hφ a T hT).integrable (by norm_num)
  have hzeroν : (∫ x in ball z R, φ x ∂ν) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hinner]
    change (∫ x in ball a T, φ x ∂μ) = 0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero houter, hzero]
  have ht := finite_truncations_tendsto_renormalized p G ν
    (globalGrowth_restrict (p + 1) G μ hg (ball a T)) e φ L hφ hφI
    (2 * T) (by positivity) (ball_restriction_pair_diameter μ a T)
    z R hR hinner hzeroν
  have heq (ε : ℝ) : (∫ x, φ x * inner ℝ e (truncated (p + 1) ν ε (fun _ => 1) x) ∂ν) =
      ∫ x, φ x * inner ℝ e
        (truncated (p + 1) μ ε ((ball a T).indicator (fun _ => 1)) x) ∂μ := by
    dsimp only [ν]
    simp_rw [truncated_restriction_eq_indicator (p + 1) μ (ball a T) measurableSet_ball]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [houter x hx, zero_mul]
  simpa only [heq] using! ht

theorem ball_indicator_one_memLp_and_sq_integral {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (T : ℝ) (hT : 0 < T) :
    MemLp ((ball a T).indicator (fun _ => (1 : ℝ))) 2 μ ∧
      (∫ x, ((ball a T).indicator (fun _ => (1 : ℝ)) x) ^ 2 ∂μ) = μ.real (ball a T) := by
  let : IsFiniteMeasure (μ.restrict (ball a T)) :=
    finiteMeasure_restrict_ball_of_globalGrowth n G μ hg a T hT
  refine ⟨(memLp_indicator_iff_restrict measurableSet_ball).mpr (memLp_const (1 : ℝ)), ?_⟩
  have heq : (fun x => ((ball a T).indicator (fun _ => (1 : ℝ)) x) ^ 2) =
      (ball a T).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ ball a T <;> simp only [indicator_of_mem, indicator_of_notMem, hx,
      not_false_eq_true, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [heq, integral_indicator measurableSet_ball, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]

end

end RieszRectifiability

end OAI
