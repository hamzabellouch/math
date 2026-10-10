import Mathlib
import OAI.Geometry.WeakHessian.Transport.RestrictCurve

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [BorelSpace X] in

lemma IsTestPlan.ae_prod_metricSpeed_lt_top {π : Measure (Curve X)} (hπ : IsTestPlan m π) :
    ∀ᵐ z ∂π.prod (volume.restrict (Set.Icc (0 : ℝ) 1)), metricSpeed z.1 z.2 < ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  have hfin : (∫⁻ z : Curve X × ℝ, metricSpeed z.1 z.2 ^ 2
      ∂π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) < ∞ := by
    rw [lintegral_prod _ (measurable_metricSpeed.pow_const 2).aemeasurable]
    exact hπ.2.2.2
  filter_upwards [ae_lt_top (measurable_metricSpeed.pow_const 2) hfin.ne] with z hz
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hz

lemma IsLocalWeakUpperGradient.of_dominated_ae_tendsto {f D B : X → ℝ} {Dn : ℕ → X → ℝ}
    (hn : ∀ n, IsLocalWeakUpperGradient m f (Dn n))
    (hD : LocallyL2 m D) (hB : LocallyL2 m B)
    (hbound : ∀ n, ∀ᵐ x ∂m, Dn n x ≤ B x)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => Dn n x) atTop (𝓝 (D x))) :
    IsLocalWeakUpperGradient m f D := by
  refine ⟨hD, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr (fun n => (hn n).2.1), hlim] with x hx hl
    exact ge_of_tendsto hl (Eventually.of_forall hx)
  · intro π hπ hb
    let : IsProbabilityMeasure π := hπ.1
    let ν := π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))
    let action : (X → ℝ) → Curve X × ℝ → ℝ≥0∞ := fun g z =>
      ENNReal.ofReal (g (evalReal z.1 z.2)) * metricSpeed z.1 z.2
    have hbfin : (∫⁻ z, action B z ∂ν) ≠ ∞ := by
      rw [lintegral_prod _ (hπ.aemeasurable_action hB)]
      exact (hπ.lintegral_action_lt_top hb hB).ne
    have hnmeas : ∀ n, AEMeasurable (action (Dn n)) ν := fun n => hπ.aemeasurable_action (hn n).1
    have habound : ∀ n, action (Dn n) ≤ᵐ[ν] action B := by
      intro n
      filter_upwards [hπ.ae_prod_eval_of_ae (hbound n)] with z hz
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hz) _
    have halim : ∀ᵐ z ∂ν, Tendsto (fun n => action (Dn n) z) atTop (𝓝 (action D z)) := by
      filter_upwards [hπ.ae_prod_eval_of_ae hlim, hπ.ae_prod_metricSpeed_lt_top] with z hz hsz
      exact (ENNReal.continuous_mul_const hsz.ne).continuousAt.tendsto.comp
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hz)
    have hi := tendsto_lintegral_of_dominated_convergence' (action B) hnmeas habound hbfin halim
    rw [← lintegral_prod _ (hπ.aemeasurable_action hD)]
    apply ge_of_tendsto hi
    exact Eventually.of_forall fun n => by
      dsimp only [action, ν]
      rw [lintegral_prod _ (hπ.aemeasurable_action (hn n).1)]
      exact (hn n).2.2 π hπ hb

end WeakHessian

end
end InlinedFile0

end OAI
