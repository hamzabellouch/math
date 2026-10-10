import OAI.Geometry.SurfaceImmersion.Atlas.ChartPushforward

namespace OAI

/-! Extension of a supported coordinate change through any smooth surface
coordinate neighborhood, including the constructed crosscap coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M]
variable {V : Type*} [NormedAddCommGroup V]

def coordinatePushforward (c : OpenPartialHomeomorph M Base) (δ : Base → V) : M → V :=
  c.source.indicator (δ ∘ c)

lemma coordinatePushforward_source (c : OpenPartialHomeomorph M Base)
    (δ : Base → V) {q : M} (hq : q ∈ c.source) :
    coordinatePushforward c δ q = δ (c q) := indicator_of_mem hq _

lemma coordinatePushforward_zero_off (c : OpenPartialHomeomorph M Base)
    (δ : Base → V) {q : M} (hq : q ∉ c.symm '' tsupport δ) :
    coordinatePushforward c δ q = 0 := by
  by_cases hs : q ∈ c.source
  · rw [coordinatePushforward_source c δ hs]
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hq ⟨c q,hz,c.left_inv hs⟩
  · exact indicator_of_notMem hs _

variable [T2Space M]

lemma coordinatePushforward_tsupport (c : OpenPartialHomeomorph M Base)
    {δ : Base → V} (hc : HasCompactSupport δ) (hs : tsupport δ ⊆ c.target) :
    tsupport (coordinatePushforward c δ) ⊆ c.symm '' tsupport δ := by
  have hK : IsCompact (c.symm '' tsupport δ) :=
    hc.image_of_continuousOn (c.continuousOn_symm.mono hs)
  apply closure_minimal _ hK.isClosed
  intro q hq
  by_contra hn
  exact hq (coordinatePushforward_zero_off c δ hn)

variable [ChartedSpace Plane M] [NormedSpace ℝ V]

lemma coordinatePushforward_smooth (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    {δ : Base → V} (hd : ContDiff ℝ ∞ δ) (hc : HasCompactSupport δ)
    (hs : tsupport δ ⊆ c.target) :
    ContMDiff planeModel 𝓘(ℝ,V) ∞ (coordinatePushforward c δ) := by
  intro q
  by_cases hq : q ∈ tsupport (coordinatePushforward c δ)
  · obtain ⟨z,hz,rfl⟩ := coordinatePushforward_tsupport c hc hs hq
    have hsource := c.map_target (hs hz)
    have hlocal := hd.contMDiff.contMDiffAt.comp _
      (hcs.contMDiffAt (c.open_source.mem_nhds hsource))
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds hsource] with y hy
    exact coordinatePushforward_source c δ hy
  · exact contMDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hq)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
