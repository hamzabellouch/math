import OAI.Analysis.CircleDomains.Transfer.ModelProjectionFibers
import OAI.Analysis.CircleDomains.Selection.PointFiberConcentration
import OAI.Analysis.CircleDomains.Topology.QuotientCollarJordan

namespace OAI

/-! The horizontal section and its priority interpolation are continuous
at every point end of the actual scalar model. No boundary extension or
upper semicontinuity assertion is an extra input. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def horizontalSection (M : CompactScalarModel G u) (q : Sphere) : ℝ :=
    (finiteCoord (invFun M.projection q)).re

 theorem horizontalSection_on_domain (M : CompactScalarModel G u)
    {q : Sphere} (hq : q ∈ G) :
    M.horizontalSection q = (finiteCoord (extendAtInfinity M.function q)).re := by
  have hh : M.projection (invFun M.projection q) = q :=
    invFun_eq ⟨extendAtInfinity M.function q, M.projection_inverse q hq⟩
  have he := (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hh
  simp only [horizontalSection, he]

 theorem horizontalSection_point_trace (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {p : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hpoint : connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p = {p}) :
    ContinuousAt M.horizontalSection (M.projection p) ∧
      M.horizontalSection (M.projection p) = (finiteCoord p).re := by
  have hfiber : M.projection ⁻¹' {M.projection p} = {p} :=
    (M.projection_fiber hsard hsch hG hconn hinf hTD hp).trans hpoint
  have hsurj := M.projection_surjective hsard hsch hG hconn hinf hTD
  have hpinf : p ≠ OnePoint.infty := by
    rintro rfl
    exact hp ⟨_, hinf, rfl⟩
  have ha : ContinuousAt (fun z : Sphere => (finiteCoord z).re) p :=
    Complex.continuous_re.continuousAt.comp
      ((continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds hpinf))
  constructor
  · exact closed_map_section_value_continuousAt M.projection_closed hfiber ha
      (invFun M.projection) (rightInverse_invFun hsurj)
  · have hh : invFun M.projection (M.projection p) ∈ M.projection ⁻¹' {M.projection p} :=
      rightInverse_invFun hsurj (M.projection p)
    rw [hfiber, mem_singleton_iff] at hh
    simp only [horizontalSection, hh]

 theorem priority_horizontalSection_point_trace (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {p : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hpoint : connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p = {p})
    (z b : ℕ → Sphere) (hz : ∀ n, M.projection (z n) = b n)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → Sphere → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (hχc : ∀ n, ContinuousAt (χ n) (M.projection p))
    (hχ : ∀ q n, χ n q ∈ Icc (0 : ℝ) 1)
    {B : ℝ} (hb : ∀ n, ‖(finiteCoord (z n)).re‖ ≤ B) :
    ContinuousAt (fun q => priorityInfiniteValue (fun n => χ n q)
      (fun n => (finiteCoord (z n)).re) (M.horizontalSection q)) (M.projection p) := by
  have hfiber : M.projection ⁻¹' {M.projection p} = {p} :=
    (M.projection_fiber hsard hsch hG hconn hinf hTD hp).trans hpoint
  have hpinf : p ≠ OnePoint.infty := by
    rintro rfl
    exact hp ⟨_, hinf, rfl⟩
  have ha : ContinuousAt (fun z : Sphere => (finiteCoord z).re) p :=
    Complex.continuous_re.continuousAt.comp
      ((continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds hpinf))
  obtain ⟨hx, hxp⟩ := M.horizontalSection_point_trace hsard hsch hG hconn hinf hTD hp hpoint
  exact priority_continuousAt_singleton_fiber M.projection_closed hfiber ha z b hz r hr χ hs hχc hχ hb hx hxp

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
