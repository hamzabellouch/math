import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

namespace OAI

/-! A compact nontrivial set has a convex average strictly closer than its diameter. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The elementary normal-structure argument needed for the isometric
fixed-point theorem. -/
theorem compact_convex_center (K : Set E) (hK : IsCompact K) (hnt : K.Nontrivial) :
    ∃ z ∈ convexHull ℝ K, ∃ r : ℝ, r < Metric.diam K ∧
      ∀ y ∈ K, ‖z - y‖ ≤ r := by
  classical
  have hne : K.Nonempty := hnt.nonempty
  have hD : 0 < Metric.diam K := Metric.diam_pos hnt hK.isBounded
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball x.val (Metric.diam K))
    (fun _ => Metric.isOpen_ball) (fun x hx =>
      Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hD⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨x, hxs, _⟩ := Set.mem_iUnion₂.mp (hs hy)
    exact ⟨x, hxs⟩
  have hN : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hsne
  let z : E := s.centerMass (fun _ => (1 : ℝ)) (fun x => x.val)
  have hz : z ∈ convexHull ℝ K := by
    apply s.centerMass_mem_convexHull (fun _ _ => zero_le_one) _ (fun x _ => x.property)
    simpa using hN
  have hzclose (y : E) (hy : y ∈ K) : ‖z - y‖ < Metric.diam K := by
    obtain ⟨a, has, hay⟩ := Set.mem_iUnion₂.mp (hs hy)
    have hsum : (∑ x ∈ s, ‖x.val - y‖) < (s.card : ℝ) * Metric.diam K := by
      calc
        (∑ x ∈ s, ‖x.val - y‖) < ∑ _x ∈ s, Metric.diam K := by
          apply Finset.sum_lt_sum
          · intro x _
            simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hK.isBounded x.property hy
          · refine ⟨a, has, ?_⟩
            simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hay
        _ = (s.card : ℝ) * Metric.diam K := by simp
    have heq : z - y = (s.card : ℝ)⁻¹ • ∑ x ∈ s, (x.val - y) := by
      dsimp [z, Finset.centerMass]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_smul, Finset.sum_sub_distrib,
        smul_sub]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN.ne', one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
    calc
      (s.card : ℝ)⁻¹ * ‖∑ x ∈ s, (x.val - y)‖ ≤
          (s.card : ℝ)⁻¹ * ∑ x ∈ s, ‖x.val - y‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN.le)
      _ < (s.card : ℝ)⁻¹ * ((s.card : ℝ) * Metric.diam K) :=
        mul_lt_mul_of_pos_left hsum (inv_pos.mpr hN)
      _ = Metric.diam K := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne
    (show ContinuousOn (fun y : E => ‖z - y‖) K from (continuous_const.sub continuous_id).norm.continuousOn)
  exact ⟨z, hz, ‖z - y‖, hzclose y hy, fun a ha => hmax ha⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
