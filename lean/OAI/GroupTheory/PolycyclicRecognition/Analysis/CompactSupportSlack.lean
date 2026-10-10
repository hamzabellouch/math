import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.Topology.Order.Compact

namespace OAI

/-! # Strict support slack inside an open height domain -/

namespace PolycyclicRecognition

open Set Metric

/-- A compact template strictly inside an open domain has a point above
its support in every nonzero weight direction. This supplies the interior
switch hypothesis for each finitely generated probe path. -/
theorem exists_above_compact_support
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (β : W →L[ℝ] ℝ) (hβ : β ≠ 0)
    (E U : Set W) (hE : IsCompact E) (hEne : E.Nonempty)
    (hU : IsOpen U) (hEU : E ⊆ U) :
    ∃ y ∈ U, sSup (β '' E) < β y := by
  have hβlin : β.toLinearMap ≠ 0 := by
    intro h
    apply hβ
    ext x
    exact congrArg (fun f : W →ₗ[ℝ] ℝ => f x) h
  obtain ⟨v, hv⟩ := (LinearMap.surjective_iff_ne_zero.mpr hβlin) 1
  obtain ⟨x, hx, hmax⟩ := hE.exists_sSup_image_eq hEne β.continuous.continuousOn
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU x (hEU hx)
  let t : ℝ := ρ / (2 * (‖v‖ + 1))
  have hden : 0 < 2 * (‖v‖ + 1) := by positivity
  have ht : 0 < t := div_pos hρ hden
  have hmul : t * (2 * (‖v‖ + 1)) = ρ := div_mul_cancel₀ _ (ne_of_gt hden)
  have hdist : dist (x + t • v) x < ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [norm_nonneg v]
  refine ⟨x + t • v, hball hdist, ?_⟩
  rw [hmax, map_add, map_smul, smul_eq_mul]
  rw [show β v = 1 from hv]
  linarith

end PolycyclicRecognition

end OAI
