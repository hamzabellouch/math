import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets

namespace OAI

/-! Extension by zero of a compactly supported coordinate correction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V]

def chartPushforward (p : M) (δ : Base → V) : M → V :=
  (chart p).source.indicator (δ ∘ chart p)

lemma chartPushforward_source (p : M) (δ : Base → V) {q : M}
    (hq : q ∈ (chart p).source) : chartPushforward p δ q = δ (chart p q) :=
  indicator_of_mem hq _

lemma chartPushforward_zero_off (p : M) (δ : Base → V) {q : M}
    (hq : q ∉ (chart p).symm '' tsupport δ) : chartPushforward p δ q = 0 := by
  by_cases hs : q ∈ (chart p).source
  · rw [chartPushforward_source p δ hs]
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hq ⟨chart p q,hz,(chart p).left_inv hs⟩
  · exact indicator_of_notMem hs _

variable [T2Space M]

lemma chartPushforward_tsupport (p : M) {δ : Base → V}
    (hc : HasCompactSupport δ) (hs : tsupport δ ⊆ (chart p).target) :
    tsupport (chartPushforward p δ) ⊆ (chart p).symm '' tsupport δ := by
  have hK : IsCompact ((chart p).symm '' tsupport δ) :=
    hc.image_of_continuousOn ((chart p).symm.continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro q hq
  by_contra hn
  exact hq (chartPushforward_zero_off p δ hn)

variable [IsManifold planeModel ∞ M] [NormedSpace ℝ V]

lemma chartPushforward_smooth (p : M) {δ : Base → V}
    (hd : ContDiff ℝ ∞ δ) (hc : HasCompactSupport δ)
    (hs : tsupport δ ⊆ (chart p).target) :
    ContMDiff planeModel 𝓘(ℝ,V) ∞ (chartPushforward p δ) := by
  intro q
  by_cases hq : q ∈ tsupport (chartPushforward p δ)
  · obtain ⟨z,hz,rfl⟩ := chartPushforward_tsupport p hc hs hq
    have hsource := (chart p).map_target (hs hz)
    have hlocal := hd.contMDiff.contMDiffAt.comp _
      ((chart_smooth p).contMDiffAt ((chart p).open_source.mem_nhds hsource))
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(chart p).open_source.mem_nhds hsource] with y hy
    exact chartPushforward_source p δ hy
  · exact contMDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hq)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
