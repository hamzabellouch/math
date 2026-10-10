import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticCrosscapIsolation
import OAI.Geometry.SurfaceImmersion.Atlas.ChartGermImmersion

namespace OAI

/-! A prepared quadratic crosscap is isolated in the fiber of its own image. -/
noncomputable section
open Set Filter Manifold Topology Metric
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem quadratic_crosscap_isolated_fiber {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection φ b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (a,t))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r,
      centeredSurfaceTaylor φ a x = centeredSurfaceTaylor φ a a → x = a := by
  obtain ⟨r,hr,hiso⟩ := centeredSurfaceTaylor_isolated_crosscap hφ a b t hz hreg
  refine ⟨r,hr,?_⟩
  intro x hx heq
  by_contra hne
  have he := centeredSurfaceTaylor_double_reflection hφ a
    (fun z hz h => (hiso z hz).mp h) hx (mem_ball_self hr) hne heq
  apply hne
  calc
    x = (2 : ℝ) • a-((2 : ℝ) • a-x) := by module
    _ = (2 : ℝ) • a-a := by rw [← he]
    _ = a := by module

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem chart_isolated_fiber {f : M → ProjectionTarget 3} (p q : M)
    (hq : p ∈ (chart q).source) {F : Base → ProjectionTarget 3}
    (he : f =ᶠ[𝓝 p] F ∘ chart q)
    {r : ℝ} (hr : 0 < r)
    (hiso : ∀ x ∈ ball (chart q p) r, F x = F (chart q p) → x = chart q p) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, f x = f p → x = p := by
  have hbase : f p = F (chart q p) := he.self_of_nhds
  have hball := ((chart q).continuousAt hq).preimage_mem_nhds
    (ball_mem_nhds (chart q p) hr)
  have hlocal : {x | f x = f p → x = p} ∈ 𝓝 p := by
    filter_upwards [he,hball,(chart q).open_source.mem_nhds hq] with x hx hxball hxsrc
    intro hfx
    apply (chart q).injOn hxsrc hq
    apply hiso _ hxball
    exact hx.symm.trans (hfx.trans hbase)
  obtain ⟨U,hU,hopen,hp⟩ := _root_.mem_nhds_iff.mp hlocal
  exact ⟨U,hopen,hp,fun x hx => hU hx⟩

theorem prepared_crosscap_isolated_fiber {f : M → ProjectionTarget 3} (p q : M)
    (hq : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, f x = f p → x = p := by
  obtain ⟨r,hr,hiso⟩ := quadratic_crosscap_isolated_fiber hφ (chart q p) b t hz hreg
  exact chart_isolated_fiber p q hq he hr hiso

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
