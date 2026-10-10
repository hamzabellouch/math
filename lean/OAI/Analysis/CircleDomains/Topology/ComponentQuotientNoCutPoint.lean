import OAI.Analysis.CircleDomains.Topology.ComponentQuotientModel
import OAI.Analysis.CircleDomains.Topology.CircleMobiusImage

namespace OAI

/-! The constructed component quotient has no cut points. Nonseparation
is proved on the source sphere and passes through the actual quotient. -/
open Set Topology
noncomputable section
namespace CircleDomainRigidity

lemma sphere_compl_singleton_connected (p : Sphere) : IsConnected ({p}ᶜ : Set Sphere) := by
  let E := pointToInfinity p
  have hi : E.symm OnePoint.infty=p := by
    rw [← pointToInfinity_apply_self p]
    exact E.symm_apply_apply p
  have hr : Set.range ((↑) : ℂ → Sphere) = {OnePoint.infty}ᶜ := by
    ext q
    cases q using OnePoint.rec <;> simp
  have hc : IsConnected ({OnePoint.infty}ᶜ : Set Sphere) := by
    rw [← hr]
    exact isConnected_range OnePoint.continuous_coe
  have himage : E.symm '' ({OnePoint.infty}ᶜ : Set Sphere) = {p}ᶜ := by
    rw [E.symm.image_compl, image_singleton, hi]
  rw [← himage]
  exact hc.image E.symm E.symm.continuous.continuousOn

lemma componentProjection_fiber_complement_connected
    {G : Set Sphere} (hG : IsOpen G) (hc : IsConnected G) (x : Sphere) :
    IsConnected (componentProjection G ⁻¹' {componentProjection G x})ᶜ := by
  have hLC : LocallyConnectedSpace Sphere := by
    let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
    let : LocallyConnectedSpace S :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
    let e : Sphere ≃ₜ S := onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)
    exact e.locallyConnectedSpace
  let := hLC
  by_cases hx : x ∈ G
  · have he : componentProjection G ⁻¹' {componentProjection G x} = {x} := by
      ext y
      constructor
      · intro hy
        rcases (componentProjection_eq G y x).mp hy with he | ⟨hyG,hyx⟩
        · exact he
        · exact False.elim ((connectedComponentIn_subset _ _ hyx) hx)
      · rintro rfl
        rfl
    rw [he]
    exact sphere_compl_singleton_connected x
  · have he : componentProjection G ⁻¹' {componentProjection G x} = connectedComponentIn Gᶜ x := by
      ext y
      constructor
      · intro hy
        rcases (componentProjection_eq G x y).mp hy.symm with he | ⟨_,hyx⟩
        · exact he ▸ mem_connectedComponentIn hx
        · exact hyx
      · intro hy
        exact ((componentProjection_eq G x y).mpr (Or.inr ⟨hx,hy⟩)).symm
    rw [he]
    exact nonseparating_complementaryComponent hG hc hx

lemma componentQuotient_no_cut_points
    {G : Set Sphere} (hG : IsOpen G) (hc : IsConnected G) (y : ComponentQuotient G) :
    IsConnected ({y}ᶜ : Set (ComponentQuotient G)) := by
  obtain ⟨x,rfl⟩ := componentProjection_surjective G y
  have h := (componentProjection_fiber_complement_connected hG hc x).image
    (componentProjection G) (componentProjection_continuous G).continuousOn
  simpa only [← preimage_compl, image_preimage_eq _ (componentProjection_surjective G)] using h

end CircleDomainRigidity

end

end OAI
