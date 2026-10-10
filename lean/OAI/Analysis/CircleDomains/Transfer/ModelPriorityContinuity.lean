import OAI.Analysis.CircleDomains.Rigidity.ModelPointTrace
import OAI.Analysis.CircleDomains.Transfer.ChartFiberConcentration

namespace OAI

/-! The actual priority horizontal coordinate is continuous on the full
finite source plane. Nonpoint ends use a terminating cutoff, and singleton
fibers use the closed projection and shrinking Euclidean supports. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem priority_horizontal_plane_continuous (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (z : ℕ → Sphere) (b : ℕ → ℂ) (hz : ∀ n, M.projection (z n) = (b n : Sphere))
    (hcover : ∀ q : ℂ, (q : Sphere) ∉ G → (M.projection ⁻¹' {(q : Sphere)}).Nontrivial →
      ∃ n, b n = q)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → ℂ → ℝ) (hχc : ∀ n, Continuous (χ n))
    (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (hχ : ∀ q n, χ n q ∈ Icc (0 : ℝ) 1)
    (hone : ∀ n, ∀ᶠ q in 𝓝 (b n), χ n q = 1)
    {K : ℝ} (hb : ∀ n, ‖(finiteCoord (z n)).re‖ ≤ K) :
    Continuous (fun q : ℂ => priorityInfiniteValue (fun n => χ n q)
      (fun n => (finiteCoord (z n)).re) (M.horizontalSection (q : Sphere))) := by
  have hsurj := M.projection_surjective hsard hsch hG hconn hinf hTD
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hnt : (M.projection ⁻¹' {(q : Sphere)}).Nontrivial
  · have hq : (q : Sphere) ∉ G := by
      intro hq
      have hsub : (M.projection ⁻¹' {(q : Sphere)}).Subsingleton := by
        intro x hx y hy
        exact ((inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hx).trans
          ((inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hy).symm
      exact hnt.not_subsingleton hsub
    obtain ⟨n, hn⟩ := hcover q hq hnt
    apply priorityInfiniteValue_continuousAt_of_one (fun n => (hχc n).continuousAt)
      (fun n => (finiteCoord (z n)).re) (fun q => M.horizontalSection (q : Sphere))
    simpa only [hn] using hone n
  · let p := invFun M.projection (q : Sphere)
    have hpq : M.projection p = (q : Sphere) := rightInverse_invFun hsurj _
    have hfiber : M.projection ⁻¹' {(q : Sphere)} = {p} := by
      ext x
      constructor
      · intro hx
        by_contra hxp
        exact hnt ⟨x, hx, p, hpq, hxp⟩
      · rintro rfl
        exact hpq
    have hpinf : p ≠ OnePoint.infty := by
      intro he
      have hi : M.projection OnePoint.infty = OnePoint.infty := by
        simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
      rw [he, hi] at hpq
      exact OnePoint.coe_ne_infty q hpq.symm
    have ha : ContinuousAt (fun p : Sphere => (finiteCoord p).re) p :=
      Complex.continuous_re.continuousAt.comp
        ((continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
          (isClosed_singleton.isOpen_compl.mem_nhds hpinf))
    have hfp : M.projection ⁻¹' {M.projection p} = {p} := by rwa [hpq]
    have hx : ContinuousAt (fun q : ℂ => M.horizontalSection (q : Sphere)) q := by
      have hh := closed_map_section_value_continuousAt M.projection_closed hfp ha
        (invFun M.projection) (rightInverse_invFun hsurj)
      rw [hpq] at hh
      exact hh.comp OnePoint.continuous_coe.continuousAt
    exact priority_continuousAt_singleton_fiber_in_chart M.projection_closed
      ((↑) : ℂ → Sphere) OnePoint.continuous_coe hpq hfiber ha z b hz r hr χ hs
      (fun n => (hχc n).continuousAt) hχ hb hx rfl

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
