import OAI.Analysis.CircleDomains.Topology.RetainedJordanSides
import OAI.Analysis.CircleDomains.Modulus.ConformalNormalization
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! The finite simply connected chart of a Jordan-hole exterior. It is
normalized at the original point at infinity, which has chart value zero. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma isSimplyConnected_sphere_jordan_exterior (H : ℂ ≃ₜ ℂ) :
    IsSimplyConnected (closedTerminalCap H)ᶜ := by
  let e : Sphere ≃ₜ Sphere := H.onePointCongr.symm.trans CannonMobius.inversion
  have hpre : e ⁻¹' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (closedTerminalCap H)ᶜ := by
    change H.onePointCongr.symm ⁻¹' (CannonMobius.inversion ⁻¹'
      (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1)) = _
    rw [inversion_preimage_unitDisk,preimage_compl,← H.onePointCongr.image_eq_preimage_symm]
    congr 1
    simp only [closedTerminalCap,closure_jordanInterior,image_image,
      Homeomorph.onePointCongr_apply,OnePoint.map_some]
  have hball : IsSimplyConnected (ball (0 : ℂ) 1) := by
    let : ContractibleSpace (ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).contractibleSpace (nonempty_ball.mpr zero_lt_one)
    change SimplyConnectedSpace (ball (0 : ℂ) 1)
    infer_instance
  rw [← hpre]
  exact e.isSimplyConnected_preimage.mpr
    (OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image.mpr hball)

lemma finite_chart_simplyConnected {S : Set Sphere} (hS : IsSimplyConnected S)
    (hi : ∞ ∉ S) : IsSimplyConnected (((↑) : ℂ → Sphere) ⁻¹' S) := by
  apply OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image.mp
  rw [image_preimage_eq_of_subset]
  · exact hS
  · intro x hx
    cases x using OnePoint.rec with
    | infty => exact (hi hx).elim
    | coe z => exact ⟨z,rfl⟩

lemma finite_chart_proper_of_complement_nontrivial {S : Set Sphere}
    (hS : Sᶜ.Nontrivial) : ((↑) : ℂ → Sphere) ⁻¹' S ≠ univ := by
  intro he
  have hsub : Sᶜ ⊆ {∞} := by
    intro x hx
    cases x using OnePoint.rec with
    | infty => rfl
    | coe z =>
      have hz : z ∈ ((↑) : ℂ → Sphere) ⁻¹' S := he.symm ▸ mem_univ z
      exact (hx hz).elim
  exact hS.not_subsingleton (fun _ hx _ hy => (mem_singleton_iff.mp (hsub hx)).trans (mem_singleton_iff.mp (hsub hy)).symm)

def jordanExteriorPlane (H : ℂ ≃ₜ ℂ) : Set ℂ :=
  ((↑) : ℂ → Sphere) ⁻¹'
    (pointToInfinity ((H 0 : ℂ) : Sphere) '' (closedTerminalCap H)ᶜ)

lemma jordan_exterior_plane_data (H : ℂ ≃ₜ ℂ) :
    IsOpen (jordanExteriorPlane H) ∧ IsSimplyConnected (jordanExteriorPlane H) ∧
      jordanExteriorPlane H ≠ univ ∧ (0 : ℂ) ∈ jordanExteriorPlane H := by
  let N := pointToInfinity ((H 0 : ℂ) : Sphere)
  have hcenter : ((H 0 : ℂ) : Sphere) ∈ closedTerminalCap H := by
    refine ⟨H 0,?_,rfl⟩
    rw [closure_jordanInterior]
    exact ⟨0,by simp,rfl⟩
  have hno : ∞ ∉ N '' (closedTerminalCap H)ᶜ := by
    rintro ⟨p,hp,he⟩
    have heq : p=((H 0 : ℂ) : Sphere) := N.injective
      (he.trans (pointToInfinity_apply_self _).symm)
    exact hp (heq.symm ▸ hcenter)
  have hnon : (N '' (closedTerminalCap H)ᶜ)ᶜ.Nontrivial := by
    rw [← N.image_compl,compl_compl]
    exact (nontrivial_closedTerminalCap H).image N.injective
  refine ⟨(N.isOpenMap _ (isCompact_closedTerminalCap H).isClosed.isOpen_compl).preimage
    OnePoint.continuous_coe, finite_chart_simplyConnected
      (N.isSimplyConnected_image.mpr (isSimplyConnected_sphere_jordan_exterior H)) hno,
    finite_chart_proper_of_complement_nontrivial hnon,?_⟩
  change ((0 : ℂ) : Sphere) ∈ N '' (closedTerminalCap H)ᶜ
  refine ⟨∞,?_,?_⟩
  · rintro ⟨z,_hz,he⟩
    exact OnePoint.coe_ne_infty z he
  · change CannonMobius.inversion (affineSphere 1 (-(H 0)) one_ne_zero ∞) = ((0 : ℂ) : Sphere)
    exact CannonMobius.inv_infty

end CircleDomainRigidity

end

end OAI
