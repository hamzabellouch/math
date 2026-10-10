import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.CostMetric

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile60
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma quadraticWassersteinSq_le_of_balls (μ ν : ProbabilityMeasure X) (a b : X) {r s : ℝ}
    (_hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hμ : ∀ᵐ x ∂(μ:Measure X),dist x a ≤ r) (hν : ∀ᵐ x ∂(ν:Measure X),dist x b ≤ s) :
    quadraticWassersteinSq (μ:Measure X) (ν:Measure X) ≤ (r+s+dist a b)^2 := by
  let q : Measure (X×X) := (μ:Measure X).prod (ν:Measure X)
  have hq : IsCoupling q μ ν := ⟨by simp [q],by simp [q]⟩
  have hc : ∀ᵐ p ∂q,dist p.1 p.2 ≤ r+s+dist a b := by
    have hu : ∀ᵐ p : X×X ∂q,dist p.1 a ≤ r := ae_of_ae_map measurable_fst.aemeasurable (by rw [hq.1]; exact hμ)
    have hv : ∀ᵐ p : X×X ∂q,dist p.2 b ≤ s := ae_of_ae_map measurable_snd.aemeasurable (by rw [hq.2]; exact hν)
    filter_upwards [hu,hv] with p hp hq
    have h1 := dist_triangle p.1 a p.2
    have h2 := dist_triangle a b p.2
    rw [dist_comm b p.2] at h2
    linarith
  have hI : Integrable (fun p : X×X => dist p.1 p.2^2) q := Integrable.of_bound (by fun_prop) ((r+s+dist a b)^2) (hc.mono fun p hp => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ dist_nonneg hp 2)
  have hqt : QuadraticTransportCost q ≠ ∞ := (cost_ne_top_iff_integrable_sq).mpr hI
  apply (quadraticWassersteinSq_le_cost hq hqt).trans
  rw [quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  apply (integral_mono_ae hI (integrable_const ((r+s+dist a b)^2))
    (hc.mono fun p hp => pow_le_pow_left₀ dist_nonneg hp 2)).trans_eq
  simp [q]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_ae_ball {m : Measure X} (u : Lp ℝ 2 m) (a : X) {r : ℝ}
    (hu : ∀ᵐ x ∂m,r < dist x a → u x = 0) :
    ∀ᵐ x ∂densityMeasure m u,dist x a ≤ r := by
  apply (ae_withDensity_iff (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal)).mpr
  filter_upwards [hu] with x hx hn
  by_contra H
  have hzero := hx (lt_of_not_ge H)
  exact hn (by rw [hzero,ENNReal.ofReal_zero])
end WeakHessian

end
end InlinedFile60

end OAI
