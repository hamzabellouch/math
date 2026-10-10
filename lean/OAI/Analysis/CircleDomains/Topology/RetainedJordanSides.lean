import OAI.Analysis.CircleDomains.Topology.JordanSideCorrespondence
import OAI.Analysis.CircleDomains.Topology.QuotientCollarJordan

namespace OAI

/-! A retained Jordan curve separates the two sides of an open connected
sphere domain. This applies to the actual finite models without extending
the model map across any terminal disk. -/

open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem isPreconnected_finite_part {G : Set Sphere}
    (hG : IsOpen G) (hconn : IsPreconnected G) :
    IsPreconnected (((↑) : ℂ → Sphere) ⁻¹' G) := by
  by_cases hi : OnePoint.infty ∈ G
  · exact (finite_part_connected_unbounded hconn
      (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hi))).1
  · have he : finiteCoord '' G = ((↑) : ℂ → Sphere) ⁻¹' G := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact (CannonMobius.coe_coordinate (fun h => hi (h ▸ hp))).symm ▸ hp
      · intro hz
        exact ⟨(z : Sphere), hz, finiteCoord_coe z⟩
    rw [← he]
    exact hconn.image _ (continuousOn_finiteCoord_of_avoids_infty hi)

 theorem isPreconnected_sphere_inter_jordan
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  have hi := isPreconnected_inter_jordanInterior
    (hG.preimage OnePoint.continuous_coe) (isPreconnected_finite_part hG hconn) H
    (fun z hz => hboundary (mem_image_of_mem _ hz))
  rw [← image_preimage_inter ((↑) : ℂ → Sphere) (jordanInterior H) G]
  exact hi.image _ OnePoint.continuous_coe.continuousOn

 theorem inversion_preimage_unitDisk :
    CannonMobius.inversion ⁻¹' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) 1)ᶜ := by
  ext p
  change CannonMobius.inv p ∈ ((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1 ↔ _
  cases p using OnePoint.rec with
  | infty => simp [CannonMobius.inv_infty]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [CannonMobius.inv_zero]
    · have he : CannonMobius.inv (z : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by
        simp [CannonMobius.inv, hz]
      rw [he]
      simpa only [OnePoint.coe_injective.mem_set_image, mem_ball, dist_zero_right,
        mem_compl_iff, mem_closedBall, not_le, norm_inv] using
        (inv_lt_one₀ (norm_pos_iff.mpr hz))

 theorem isPreconnected_sphere_inter_jordan_exterior
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (closedTerminalCap H)ᶜ) := by
  let e : Sphere ≃ₜ Sphere := H.onePointCongr.symm.trans CannonMobius.inversion
  have hpre : e ⁻¹' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (closedTerminalCap H)ᶜ := by
    change H.onePointCongr.symm ⁻¹' (CannonMobius.inversion ⁻¹'
      (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1)) = _
    rw [inversion_preimage_unitDisk, preimage_compl, ← H.onePointCongr.image_eq_preimage_symm]
    congr 1
    simp only [closedTerminalCap, closure_jordanInterior, image_image,
      Homeomorph.onePointCongr_apply, OnePoint.map_some]
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Homeomorph.refl ℂ)) ⊆ e '' G := by
    rintro p ⟨z, hz, rfl⟩
    have hzn : ‖z‖ = 1 := by simpa [frontier_jordanInterior] using hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hzn
    refine ⟨(H z⁻¹ : ℂ), hboundary ?_, ?_⟩
    · refine ⟨H z⁻¹, ?_, rfl⟩
      rw [frontier_jordanInterior]
      exact ⟨z⁻¹, by simp [norm_inv, hzn], rfl⟩
    · change CannonMobius.inv (H.onePointCongr.symm ((H z⁻¹ : ℂ) : Sphere)) = (z : Sphere)
      have hx : H.onePointCongr.symm ((H z⁻¹ : ℂ) : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by
        change H.onePointCongr.symm (H.onePointCongr ((z⁻¹ : ℂ) : Sphere)) = _
        exact H.onePointCongr.symm_apply_apply _
      rw [hx]
      simp [CannonMobius.inv, hz0]
  have hc := isPreconnected_sphere_inter_jordan (e.isOpenMap G hG)
    (hconn.image e e.continuous.continuousOn) (Homeomorph.refl ℂ) hbd
  have he : e.symm '' (e '' G ∩ (((↑) : ℂ → Sphere) ''
      jordanInterior (Homeomorph.refl ℂ))) = G ∩ (closedTerminalCap H)ᶜ := by
    rw [e.symm.image_eq_preimage_symm, Homeomorph.symm_symm, preimage_inter,
      e.injective.preimage_image]
    simpa only [jordanInterior, Homeomorph.refl_apply, image_id] using
      congrArg (G ∩ ·) hpre
  rw [← he]
  exact hc.image e.symm e.symm.continuous.continuousOn

 theorem open_image_retained_jordan_side_eq
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) (H J : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty)
    (hboundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J)) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
  let A : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior H
  let B : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  have hAo : IsOpen A := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hBo : IsOpen B := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hAf : frontier A = ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) :=
    frontier_sphere_image_jordanInterior H
  have hBf : frontier B = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) :=
    frontier_sphere_image_jordanInterior J
  have hAcl : closure A = closedTerminalCap H := closure_sphere_image_jordanInterior H
  have havoid (x : Sphere) (hx : x ∈ G) (hxA : x ∉ frontier A) : f x ∉ frontier B := by
    intro hy
    rw [hBf, ← hboundary] at hy
    obtain ⟨y, hy, he⟩ := hy
    have hyx := hi (hbd hy) hx he
    exact hxA (hAf.symm ▸ (hyx ▸ hy))
  have hsplit (S : Set Sphere) (hS : S ⊆ G) (ha : Disjoint S (frontier A)) :
      f '' S ⊆ B ∪ (closure B)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hb : f x ∈ B
    · exact Or.inl hb
    · exact Or.inr (fun hc => havoid x (hS hx)
        (fun h => Set.disjoint_left.mp ha hx h) ⟨hc, hBo.interior_eq.symm ▸ hb⟩)
  have hdisj : Disjoint B (closure B)ᶜ :=
    Set.disjoint_left.mpr (fun _ h h' => h' (subset_closure h))
  have houtside : f '' (G ∩ (closure A)ᶜ) ⊆ (closure B)ᶜ := by
    have hc : IsPreconnected (f '' (G ∩ (closure A)ᶜ)) :=
      ((hAcl.symm ▸ isPreconnected_sphere_inter_jordan_exterior hG hconn H hbd).image
        f (hf.mono inter_subset_left))
    apply hc.subset_right_of_subset_union hBo isClosed_closure.isOpen_compl hdisj
      (hsplit _ inter_subset_left (Set.disjoint_left.mpr (fun (x : Sphere) (h : x ∈ G ∩ (closure A)ᶜ)
        (h' : x ∈ frontier A) => h.2 (frontier_subset_closure h'))))
    refine ⟨OnePoint.infty, ?_, ?_⟩
    · refine ⟨OnePoint.infty, ⟨hinf, ?_⟩, hfix⟩
      rw [hAcl]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
    · rw [closure_sphere_image_jordanInterior J]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
  have hinverse : f '' G ∩ B ⊆ f '' (G ∩ A) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hb⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    by_contra hxA
    by_cases hxc : x ∈ closure A
    · have hxf : x ∈ frontier A := ⟨hxc, hAo.interior_eq.symm ▸ hxA⟩
      have hyf : f x ∈ frontier B := by
        rw [hBf, ← hboundary]
        exact mem_image_of_mem f (hAf ▸ hxf)
      exact hyf.2 (hBo.interior_eq.symm ▸ hb)
    · exact houtside (mem_image_of_mem f ⟨hx, hxc⟩) (subset_closure hb)
  have hmeet : (f '' (G ∩ A) ∩ B).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior H).nonempty
    have hzA : (z : Sphere) ∈ frontier A := hAf.symm ▸ mem_image_of_mem _ hz
    have hzG : (z : Sphere) ∈ G := hbd (mem_image_of_mem _ hz)
    have hzf : f (z : Sphere) ∈ frontier B := by
      rw [hBf, ← hboundary]
      exact mem_image_of_mem f (mem_image_of_mem _ hz)
    obtain ⟨y, hy, hyB⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hzf)
      (f '' G) ((ho G hG Subset.rfl).mem_nhds (mem_image_of_mem f hzG))
    exact ⟨y, hinverse ⟨hy, hyB⟩, hyB⟩
  have hins : f '' (G ∩ A) ⊆ B := by
    apply ((isPreconnected_sphere_inter_jordan hG hconn H hbd).image
      f (hf.mono inter_subset_left)).subset_left_of_subset_union
      hBo isClosed_closure.isOpen_compl hdisj
      (hsplit _ inter_subset_left (Set.disjoint_left.mpr (fun _ h h' =>
        h'.2 (hAo.interior_eq.symm ▸ h.2)))) hmeet
  exact Subset.antisymm (fun _ h => ⟨image_mono inter_subset_left h, hins h⟩) hinverse

end CircleDomainRigidity

end

end OAI
