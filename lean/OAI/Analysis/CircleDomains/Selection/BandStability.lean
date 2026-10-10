import OAI.Analysis.CircleDomains.Uniformization.BandLimits
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Group.Lemmas
import Mathlib.Analysis.Normed.Group.Real

namespace OAI

/-!
# Stability of bands under boundary-vanishing approximation

The smoothing step in Section 6 changes a coordinate by an error tending
to zero at every dust point. Its cluster values, interval bands and
mod-one level incidences at those points are therefore exactly preserved.
No regularity of either coordinate on the dust is required.
-/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem tendsto_difference_of_vanishing_tolerance
    {X : Type*} [TopologicalSpace X] {G : Set X} {f g e : X → ℝ} {x : X}
    (he : Tendsto e (𝓝[G] x) (𝓝 0))
    (herror : ∀ y ∈ G, |f y - g y| ≤ e y) :
    Tendsto (fun y => f y - g y) (𝓝[G] x) (𝓝 0) := by
  apply squeeze_zero_norm' (f := fun y => f y - g y) _ he
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa only [Real.norm_eq_abs] using herror y hy

/-- The distance-to-dust tolerance used for smoothing really vanishes
at every dust point, including accumulation points of the dust. -/
theorem tendsto_difference_of_distance_to_dust
    {X : Type*} [MetricSpace X] {G B : Set X} {f g : X → ℝ}
    {x : X} (hx : x ∈ B) {C : ℝ}
    (herror : ∀ y ∈ G, |f y - g y| ≤ C * Metric.infDist y B) :
    Tendsto (fun y => f y - g y) (𝓝[G] x) (𝓝 0) := by
  apply tendsto_difference_of_vanishing_tolerance _ herror
  have h := (tendsto_const_nhds (x := C)).mul
    ((Metric.continuous_infDist_pt B).continuousAt.continuousWithinAt (s := G) (x := x))
  simpa only [Metric.infDist_zero_of_mem hx, mul_zero] using h

theorem mapClusterPt_of_vanishing_difference
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {G : Set X} {f g : X → ℝ} {x : X} {t : ℝ}
    (herr : Tendsto (fun y => f y - g y) (𝓝[G] x) (𝓝 0))
    (ht : MapClusterPt t (𝓝[G] x) f) : MapClusterPt t (𝓝[G] x) g := by
  obtain ⟨v, hfv, hv⟩ := ht.exists_seq_tendsto
  have hgv : Tendsto (g ∘ v) atTop (𝓝 t) := by
    have h := hfv.sub (herr.comp hv)
    convert h using 1 <;> simp only [Function.comp_def, sub_sub_cancel, sub_zero]
  exact hgv.mapClusterPt.of_comp hv

theorem clusterGraph_fiber_eq_of_vanishing_difference
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {G : Set X} {f g : X → ℝ} {x : X}
    (herr : Tendsto (fun y => f y - g y) (𝓝[G] x) (𝓝 0)) :
    {t : ℝ | (x, t) ∈ clusterGraph G f} = {t : ℝ | (x, t) ∈ clusterGraph G g} := by
  ext t
  simp only [mem_ofPred_eq, mem_clusterGraph_iff_mapClusterPt]
  constructor
  · exact mapClusterPt_of_vanishing_difference herr
  · apply mapClusterPt_of_vanishing_difference
    simpa only [neg_sub, neg_zero] using herr.neg

theorem intervalBand_fiber_eq_of_vanishing_difference
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {G : Set X} {f g : X → ℝ} {x : X}
    (herr : Tendsto (fun y => f y - g y) (𝓝[G] x) (𝓝 0)) :
    {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph G f)} =
      {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph G g)} := by
  have heq := clusterGraph_fiber_eq_of_vanishing_difference herr
  have hfib (r : ℝ) : (x, r) ∈ clusterGraph G f ↔ (x, r) ∈ clusterGraph G g :=
    Set.ext_iff.mp heq r
  ext t
  simp only [mem_ofPred_eq, mem_intervalFiberHull_iff, hfib]

theorem circleBand_fiber_eq_of_vanishing_difference
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {G : Set X} {f g : X → ℝ} {x : X}
    (herr : Tendsto (fun y => f y - g y) (𝓝[G] x) (𝓝 0)) :
    {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} =
      {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G g} := by
  have heq := intervalBand_fiber_eq_of_vanishing_difference herr
  have hfib (r : ℝ) : (x, r) ∈ intervalFiberHull (clusterGraph G f) ↔
      (x, r) ∈ intervalFiberHull (clusterGraph G g) := Set.ext_iff.mp heq r
  ext t
  constructor <;> rintro ⟨⟨y, r⟩, hr, hout⟩
  · have hy : y = x := congrArg Prod.fst hout
    subst y
    have ht := congrArg Prod.snd hout
    exact ⟨(x, r), (hfib r).mp hr, Prod.ext rfl ht⟩
  · have hy : y = x := congrArg Prod.fst hout
    subst y
    have ht := congrArg Prod.snd hout
    exact ⟨(x, r), (hfib r).mpr hr, Prod.ext rfl ht⟩

end CircleDomainRigidity

end OAI
