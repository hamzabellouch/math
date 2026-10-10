import OAI.Analysis.CircleDomains.Topology.FiniteJordanUniformization
import OAI.Analysis.CircleDomains.Topology.PlaneHomeomorphFromSphere

namespace OAI

/-! Finite Jordan uniformization also applies after an arbitrary sphere
homeomorphism. A conformal normalization makes its image of infinity the
point at infinity, leaving an actual plane homeomorphism of all caps. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma spherePlaneHomeomorph_onePointCongr (e : Sphere ≃ₜ Sphere)
    (he : e OnePoint.infty=OnePoint.infty) :
    (spherePlaneHomeomorph e he).onePointCongr=e := by
  ext p
  cases p using OnePoint.rec with
  | infty => exact he.symm
  | coe z => exact coe_spherePlaneMap e he z

lemma trans_closed_jordan_image (H P : ℂ ≃ₜ ℂ) :
    closure (jordanInterior (H.trans P))=P '' closure (jordanInterior H) := by
  change closure ((P ∘ H) '' _) = P '' closure (H '' _)
  rw [image_comp,P.image_closure]

lemma exists_finite_jordan_image_uniformization {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (e : Sphere ≃ₜ Sphere) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f (e '' C.region) V := by
  let N : Sphere ≃ₜ Sphere := pointToInfinity (e OnePoint.infty)
  let E : Sphere ≃ₜ Sphere := e.trans N
  have hE : E OnePoint.infty=OnePoint.infty := by
    exact pointToInfinity_apply_self (e OnePoint.infty)
  let P : ℂ ≃ₜ ℂ := spherePlaneHomeomorph E hE
  have hP : P.onePointCongr=E := spherePlaneHomeomorph_onePointCongr E hE
  let C' : FiniteJordanConfiguration I := {
    hole := fun i => (C.hole i).trans P
    disjoint := by
      intro i j hij
      change Disjoint (closure (jordanInterior ((C.hole i).trans P)))
        (closure (jordanInterior ((C.hole j).trans P)))
      rw [trans_closed_jordan_image,trans_closed_jordan_image]
      exact (C.disjoint hij).image P.injective.injOn (subset_univ _) (subset_univ _) }
  have hcap (i : I) : E '' closedTerminalCap (C.hole i)=closedTerminalCap (C'.hole i) := by
    rw [←hP,closedTerminalCap,CannonSphereReflection.onePoint_image]
    change ((↑) : ℂ → Sphere) '' (P '' closure (jordanInterior (C.hole i)))=_
    rw [←trans_closed_jordan_image]
    rfl
  have hreg : C'.region=E '' C.region := by
    change (⋃i,closedTerminalCap (C'.hole i))ᶜ=E '' (⋃i,closedTerminalCap (C.hole i))ᶜ
    rw [E.image_compl,image_iUnion]
    simp_rw [hcap]
  have hreg' : C'.region=N '' (e '' C.region) := by
    rw [hreg,image_image]
    rfl
  obtain ⟨V,f,hV,hf⟩ := exists_finite_jordan_uniformization C'
  rw [hreg'] at hf
  exact ⟨V,f ∘ N,hV,(isConformalEquivalence_pointToInfinity (e OnePoint.infty)
    (e '' C.region)).trans hf⟩

lemma uniformize_constructed_finite_completion_after_homeomorphism
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {W : Set Sphere} (e : Sphere ≃ₜ Sphere)
    (hW : W ⊆ openCompletedRegion H) (he : IsConformalOn e W) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ BijOn f (openCompletedRegion H) V ∧ IsConformalOn f W ∧
        IsConformalEquivalence (f ∘ e.symm) (e '' openCompletedRegion H) V := by
  obtain ⟨V,g,hV,hg⟩ := exists_finite_jordan_image_uniformization ⟨H,hd⟩ e
  change IsConformalEquivalence g (e '' openCompletedRegion H) V at hg
  refine ⟨V,g ∘ e,hV,hg.bijOn.comp e.injective.bijOn_image,
    hg.1.comp he (fun p hp => ⟨p,hW hp,rfl⟩),?_⟩
  have heq : (g ∘ e) ∘ e.symm=g := by funext p; simp only [comp_apply,e.apply_symm_apply]
  simpa only [heq] using hg

end CircleDomainRigidity

end

end OAI
