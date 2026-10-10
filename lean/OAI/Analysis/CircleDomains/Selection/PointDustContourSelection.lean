import OAI.Analysis.CircleDomains.Selection.SubordinateDustCover
import OAI.Analysis.CircleDomains.Transfer.PointDustModels
import OAI.Analysis.CircleDomains.Topology.SpherePlaneContinuity

namespace OAI

/-! The existing subordinate contour construction on a point-complement
source, with its identity quotient made explicit. -/
open Set Function Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem continuous_sphereFromPlaneFunction {p : EuclideanPlane → ℝ}
    (hp : Continuous p) (hs : HasCompactSupport p) : Continuous (sphereFromPlaneFunction p) := by
  exact continuousOn_univ.mp (sphereFromPlaneFunction_continuousOn isOpen_univ hp.continuousOn
    hs.isCompact (fun _ hx => image_eq_zero_of_notMem_tsupport hx))

 theorem exists_point_dust_subordinate_contours
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) {G W : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hW : IsOpen W) (hBW : Gᶜ ⊆ W)
    (Q : {z : Sphere // z ∈ Gᶜ} → Set Sphere)
    (hQ : ∀ a, IsOpen (Q a)) (haQ : ∀ a, a.val ∈ Q a) :
    ∃ (n : ℕ) (J : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      ({z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i)) ∧
      ∀ i, closure (jordanInterior (J i)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (J i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (J i)), (z : Sphere) ∈ G) ∧
        ∃ a : {z : Sphere // z ∈ Gᶜ}, closure (jordanInterior (J i)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' Q a := by
  have hr : ∀ z w : Sphere, id z = id w ↔ z = w ∨
      (z ∈ Gᶜ ∧ w ∈ connectedComponentIn Gᶜ z) := by
    intro z w
    constructor
    · exact Or.inl
    · rintro (he | he)
      · exact he
      · exact (point_component_eq_of_totallyDisconnected hTD z w he.2).symm
  obtain ⟨n,J,γ,hcover,_,hdata⟩ := exists_subordinate_smooth_physical_dust_cover
    hsard hsch G id continuous_id (Homeomorph.refl Sphere).isClosedMap surjective_id
    (B := Gᶜ) (A := Gᶜ) (W := W) hr hG.isClosed_compl hTD hG.isClosed_compl.isCompact
    (subset_refl _) (by rw [sdiff_self]; exact isClosed_empty) hW hBW
    (not_not.mpr hinf) (fun _ hx => hx) Q hQ haQ
  refine ⟨n,J,γ,hcover,?_⟩
  intro i
  obtain ⟨hi,hs,he,hfront,ha,hsub⟩ := hdata i
  exact ⟨hi,hs,he,hfront,fun z hz => (ha z hz).1,hsub⟩

end CircleDomainRigidity

end

end OAI
