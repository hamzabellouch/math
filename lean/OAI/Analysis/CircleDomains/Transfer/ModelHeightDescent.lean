import OAI.Analysis.CircleDomains.Rigidity.ModelPointTrace
import OAI.Analysis.CircleDomains.Topology.ClosedMapDescent
import OAI.Analysis.CircleDomains.Topology.ModelHeightComponents
import OAI.Analysis.CircleDomains.Selection.ControlledHeight

namespace OAI

/-! The constructed conductivity height descends continuously through
the actual source projection, including every nonpoint end. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_constant_on_sphere_components (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    {p q : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hq : q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p) :
    H.height (finiteCoord p) = H.height (finiteCoord q) := by
  have hqout := connectedComponentIn_subset _ _ hq
  cases p using OnePoint.rec with
  | infty => exact (hp ⟨_, hinf, rfl⟩).elim
  | coe z =>
    cases q using OnePoint.rec with
    | infty => exact (hqout ⟨_, hinf, rfl⟩).elim
    | coe w =>
      have hp' : complexPlaneCoordinates.symm z ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) := by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere, complexPlaneCoordinates.apply_symm_apply] using hp
      have hq' : planeSphere (complexPlaneCoordinates.symm w) ∈
          connectedComponentIn (extendAtInfinity M.function '' G)ᶜ (planeSphere (complexPlaneCoordinates.symm z)) := by
        simpa only [planeSphere, complexPlaneCoordinates.apply_symm_apply] using hq
      simpa only [finiteCoord_coe, complexPlaneCoordinates.apply_symm_apply] using
        M.height_constant_on_components hinf H.height.continuous
          (heightLimitGradient H.error₀ H.error₁) H.weak_gradient
          (fun r i => (heightLimitWitness H.error₀ H.error₁
            (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient r).weakGrad_component_memLp i)
          hHz hp' hq'

 def heightSection (M : CompactScalarModel G u) {R d : ℝ} (H : ControlledHeight R d) (q : Sphere) : ℝ :=
    H.height (finiteCoord (invFun M.projection q))

 theorem heightSection_continuousAt_end (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    {q : Sphere} (hq : q ∈ Gᶜ) (hqinf : q ≠ OnePoint.infty) :
    ContinuousAt (M.heightSection H) q := by
  have hsurj := M.projection_surjective hsard hsch hG hconn hinf hTD
  let p := invFun M.projection q
  have hpq : M.projection p = q := rightInverse_invFun hsurj q
  have hpOut : p ∉ extendAtInfinity M.function '' G := by
    rintro ⟨x, hx, he⟩
    have hpx : M.projection p = x := by rw [← he, M.projection_inverse x hx]
    have heq : x = q := hpx.symm.trans hpq
    exact hq (heq ▸ hx)
  apply (closed_map_section_continuousAt_of_fiber M.projection_closed (invFun M.projection)
    (rightInverse_invFun hsurj) (a := fun z => H.height (finiteCoord z)) (v := H.height (finiteCoord p)) ?_ ?_).1
  · intro z hz
    have hzinf : z ≠ OnePoint.infty := by
      intro he
      have hi : M.projection OnePoint.infty = OnePoint.infty := by
        simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
      rw [he, hi] at hz
      exact hqinf hz.symm
    exact H.height.continuous.continuousAt.comp
      ((continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds hzinf))
  · intro z hz
    have hzp : z ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p := by
      rw [← M.projection_fiber hsard hsch hG hconn hinf hTD hpOut]
      exact hz.trans hpq.symm
    exact (M.height_constant_on_sphere_components hinf H hHz hpOut hzp).symm

 theorem heightSection_on_domain (M : CompactScalarModel G u) {R d : ℝ}
    (H : ControlledHeight R d) {q : Sphere} (hq : q ∈ G) :
    M.heightSection H q = H.height (finiteCoord (extendAtInfinity M.function q)) := by
  have hh : M.projection (invFun M.projection q) = q :=
    invFun_eq ⟨extendAtInfinity M.function q, M.projection_inverse q hq⟩
  have he := (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hh
  simp only [heightSection, he]

 theorem heightSection_continuousAt (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    {q : Sphere} (hqinf : q ≠ OnePoint.infty) :
    ContinuousAt (M.heightSection H) q := by
  by_cases hq : q ∈ G
  · have hsurj := M.projection_surjective hsard hsch hG hconn hinf hTD
    have hsingle (z : Sphere) (hz : M.projection z = q) :
        z = extendAtInfinity M.function q :=
      (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hz
    apply (closed_map_section_continuousAt_of_fiber M.projection_closed (invFun M.projection)
      (rightInverse_invFun hsurj) (a := fun z => H.height (finiteCoord z))
      (v := H.height (finiteCoord (extendAtInfinity M.function q))) ?_ ?_).1
    · intro z hz
      have hzinf : z ≠ OnePoint.infty := by
        intro he
        have hi : M.projection OnePoint.infty = OnePoint.infty := by
          simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
        rw [he, hi] at hz
        exact hqinf hz.symm
      exact H.height.continuous.continuousAt.comp
        ((continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
          (isClosed_singleton.isOpen_compl.mem_nhds hzinf))
    · intro z hz
      rw [hsingle z hz]
  · exact M.heightSection_continuousAt_end hsard hsch hG hconn hinf hTD H hHz hq hqinf

 theorem heightSection_plane_continuous (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0) :
    Continuous (fun z : ℂ => M.heightSection H (z : Sphere)) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (M.heightSection_continuousAt hsard hsch hG hconn hinf hTD H hHz
    (OnePoint.coe_ne_infty z)).comp OnePoint.continuous_coe.continuousAt

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
