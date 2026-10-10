import OAI.Geometry.NodalSets.Charts.ChartedEnvelope

namespace OAI

namespace Yau.Geometry
open scoped ContDiff Topology
open Yau.Jets MvPolynomial Filter
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

theorem actual_metric_chart_phase_contact {s : Set T} (hcompact : IsCompact s)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → Coord) (hy : Continuous y) (e : T → Coord ≃L[ℝ] Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    (q : T → Coord) (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, b t ≠ 0)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, b t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t ∈ s, 0 < sourceHessian g S (y t)
      (metricGradient g S (y t)) (metricGradient g S (y t)) + sourceHessian g S (y t) (q t) (q t))
    (P : T → CPoly) (hP : ContinuousPolyFamily P)
    (hkeep : ∀ t ∈ s, ∀ k, k ≤ 2 → homogeneousComponent k (P t) =
      initialPhaseJet (S (y t)) (normalFrameVector (a t) (b t))
        (normalComplexHessian (a t) (b t)
          (envelopeHessian (S ∘ actualMetricChart g (y t) (e t)))) k) :
    ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ 2*N^(-1/3:ℝ) →
      (reval (P t) x).re-S (actualMetricChart g (y t) (e t) x) ≤ -c*‖x‖^2 := by
  let S' : T → Coord → ℝ := fun t ↦ S ∘ actualMetricChart g (y t) (e t)
  have hS' (t : T) : ContDiff ℝ ∞ (S' t) := hS.comp (quadraticChartMap_smooth _ _ _)
  have hB := actualFrameConnection_continuous g hg hp y hy e he
  have hsc (k : ℕ) : Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (S' z.1) z.2) :=
    charted_scalar_spatial_jets S hS y hy e he _ hB k
  have hd t ht := charted_envelope_adapted_data g hg hs hp S hS (y t) (e t) (ho t)
    (q t) (a t) (b t) (hap t) (hbq t) (hstrict t ht)
  apply retained_phase_uniform_contact hcompact P hP S' hS' hsc a b ha hb ha0 hb0
    (envelopeHessian_family_continuous S' (hsc 2))
    (fun t ht ↦ (hd t ht).1) _ (fun t ht ↦ (hd t ht).2)
  intro t ht k hk
  simpa only [S', Function.comp_apply, actualMetricChart, quadraticChart_coe,
    quadraticChartMap_zero] using hkeep t ht k hk

end
end Yau.Geometry

end OAI
