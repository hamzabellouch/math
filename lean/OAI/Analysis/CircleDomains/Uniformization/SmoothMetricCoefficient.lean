import OAI.Analysis.CircleDomains.Uniformization.MetricBeltramiLinear
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace OAI

/-! The actual compactly supported smooth coefficient of the prescribed
metric, in the complex plane used by the existing Beltrami solver. -/
open Set
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_smooth_metric_coefficient
    (g : (ℝ × ℝ) → PlanarMetric) (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ x, (g x).PosDef)
    (hfar : ∃ R : ℝ, 0 < R ∧ ∀ x ∉ Metric.closedBall 0 R,
      ∃ r : ℝ, g x = r • 1) :
    ∃ μ : SchwartzMap ℂ ℂ, HasCompactSupport (μ : ℂ → ℂ) ∧
      (∀ z, μ z = metricBeltramiCoefficient (g (Complex.equivRealProdCLM z))) ∧
      ∃ k : ℝ≥0, k < 1 ∧ ∀ z, ‖μ z‖ ≤ k := by
  obtain ⟨R, hR, hfar⟩ := hfar
  let u : ℂ → ℂ := fun z => metricBeltramiCoefficient (g (Complex.equivRealProdCLM z))
  have hu : ContDiff ℝ ∞ u :=
    (contDiff_metricBeltramiCoefficient hg hPD).comp Complex.equivRealProdCLM.contDiff
  have hs : HasCompactSupport u :=
    (metricBeltramiCoefficient_compact_support hfar).comp_homeomorph
      Complex.equivRealProdCLM.toHomeomorph
  obtain ⟨k, hk, hbound⟩ := metricBeltramiCoefficient_uniform_bound hg hPD hR hfar
  exact ⟨hs.toSchwartzMap hu, hs, fun _ => rfl, k, hk,
    fun z => hbound (Complex.equivRealProdCLM z)⟩

end CircleDomainRigidity

end

end OAI
