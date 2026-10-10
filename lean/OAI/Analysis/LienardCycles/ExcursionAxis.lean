import OAI.Analysis.LienardCycles.OpenArchAxis

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow
lemma IsRightExcursion.axis_peak {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (hn : ∃ s t,z s≠z t) (he : IsRightExcursion z s t) :
    ∃ H ∈ transversePeaks a,axisEndpoint a false H=(z t).2 ∧ axisEndpoint a true H=(z s).2 := by
  obtain ⟨u,huc,hul,hur,hud,_⟩ := he.graph hF hz
  have hu : IsOpenArch (φ a) u (z t).2 (z s).2 :=
    ⟨he.y_lt hz,huc,hul,hur,fun y hy=>(hud y hy).1,fun y hy=>(hud y hy).2⟩
  obtain ⟨H,hH,hp,hpeak,_⟩ := hu.peak_exists
  obtain ⟨hl,hr⟩ := hu.axis_endpoints (φ_smooth a) (φ_continuous a).continuousOn hH hp hpeak
  have hs := he.endpoint_signs hz hn
  refine ⟨H,⟨hH,?_,?_⟩,hl,hr⟩
  · change axisLower (φ a) H<poly a 0
    rw [hl,←hF]
    exact hs.1
  · change poly a 0<axisUpper (φ a) H
    rw [hr,←hF]
    exact hs.2
namespace AxisFlow
lemma axisLower_strictAnti (a : Fin 6 → ℝ) : StrictAntiOn (axisEndpoint a false) (transversePeaks a) := by
  apply strictAntiOn_of_deriv_neg (convex_iff_ordConnected.mpr (transversePeaks_ordConnected a))
    (fun t ht=>(axisEndpoint_analytic a false ht.1 ht.2.1.ne).continuousAt.continuousWithinAt)
  intro t ht
  exact axisEndpoint_sign a false (interior_subset ht).1 (interior_subset ht).2.1.ne
lemma axisUpper_strictMono (a : Fin 6 → ℝ) : StrictMonoOn (axisEndpoint a true) (transversePeaks a) := by
  apply strictMonoOn_of_deriv_pos (convex_iff_ordConnected.mpr (transversePeaks_ordConnected a))
    (fun t ht=>(axisEndpoint_analytic a true ht.1 ht.2.2.ne').continuousAt.continuousWithinAt)
  intro t ht
  exact axisEndpoint_sign a true (interior_subset ht).1 (interior_subset ht).2.2.ne'
lemma axis_order {a : Fin 6 → ℝ} {s t : ℝ} (hs : s ∈ transversePeaks a) (ht : t ∈ transversePeaks a) :
    (axisEndpoint a true s≤axisEndpoint a true t ↔ axisEndpoint a false t≤axisEndpoint a false s) := by
  constructor
  · intro h
    have hst : s≤t := by
      by_contra! hn
      exact (not_lt_of_ge h) (axisUpper_strictMono a ht hs hn)
    exact (axisLower_strictAnti a).antitoneOn hs ht hst
  · intro h
    have hst : s≤t := by
      by_contra! hn
      exact (not_lt_of_ge h) (axisLower_strictAnti a ht hs hn)
    exact (axisUpper_strictMono a).monotoneOn hs ht hst
end AxisFlow
end QuinticLienard

end OAI
