import OAI.Analysis.CircleDomains.Rigidity.RemovableNormalizedExtension
import OAI.Analysis.CircleDomains.Rigidity.ConductivityExterior
import OAI.Analysis.CircleDomains.Topology.HolomorphicHomeomorph

namespace OAI

/-! A compact removable set in the finite chart has zero planar area.
A principal real Beltrami solution with conductivity two on that set
must be the identity. Uniqueness of its weak derivatives then forces
the set to be null. Only the already recorded principal Beltrami input
is used. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 private theorem weak_coordinate_one (i : Fin 2) (R : ℝ) :
    DeGiorgi.HasWeakPartialDeriv i (fun _ : EuclideanPlane => (1 : ℝ))
      (fun x => x i) (ball 0 R) := by
  let L : EuclideanPlane →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap
  have hL : (fun x : EuclideanPlane => x i) = L := rfl
  have hh := weakPartial_of_smooth_on (U := ball 0 R) isOpen_ball L.contDiff.contDiffOn i
  have hd : (fun x => fderiv ℝ L x (EuclideanSpace.single i 1)) =
      (fun _ : EuclideanPlane => (1 : ℝ)) := by
    funext x
    rw [L.fderiv]
    simp [L]
  rw [hd] at hh
  simpa only [hL] using hh

 theorem removable_physical_compact_volume_zero
    (hprincipal : PrincipalRealBeltrami) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hrem : IsConformallyRemovable (planeSphere '' K)) :
    volume K = 0 := by
  obtain ⟨φ,D,ht,hsys,hh,hbig⟩ := exists_principal_conductivity_holomorphic hprincipal hK 2 (by omega)
  let G := (planeSphere '' K)ᶜ
  have hG : IsOpen G := (hK.image continuous_planeSphere).isClosed.isOpen_compl
  have hinf : OnePoint.infty ∈ G := by
    rintro ⟨x,hx,he⟩
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) he
  have hsets : (((↑) : ℂ → Sphere) '' (complexPlaneCoordinates '' K)ᶜ ∪ {OnePoint.infty}) = G := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [G,planeSphere]
    | coe z => simp [G,planeSphere]
  have hconf : IsConformalOn φ.onePointCongr G := by
    rw [← hsets]
    exact holomorphicHomeomorph_conformal φ
      (hK.image complexPlaneCoordinates.continuous).isClosed.isOpen_compl hh hbig
  have hext : (φ.onePointCongr : Sphere → Sphere) = extendAtInfinity φ := by
    funext p
    cases p using OnePoint.rec <;> rfl
  have hnorm : IsPrincipalNormalized φ.onePointCongr := by
    rw [hext]
    exact isPrincipalNormalized_extendAtInfinity hbig
  have hid := removable_normalized_extension_eq_id hG hinf
    (by simpa only [G,compl_compl] using hrem) hconf hnorm φ.onePointCongr
    (fun _ _ => rfl)
  have hφ (z : ℂ) : φ z = z := OnePoint.coe_injective (hid (z : Sphere))
  obtain ⟨R,hKR⟩ := hK.isBounded.subset_ball (0 : EuclideanPlane)
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) R)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
  have hwR : DeGiorgi.HasWeakPartialDeriv (0 : Fin 2)
      (fun x => D.realGradient x 0) (fun x : EuclideanPlane => x 0) (ball 0 R) := by
    simpa only [hφ,complexPlaneCoordinates_apply] using
      weakPartial_restrict_from_univ (D.real_weak 0) (ball 0 R)
  have hwI : DeGiorgi.HasWeakPartialDeriv (1 : Fin 2)
      (fun x => D.imagGradient x 1) (fun x : EuclideanPlane => x 1) (ball 0 R) := by
    simpa only [hφ,complexPlaneCoordinates_apply] using
      weakPartial_restrict_from_univ (D.imag_weak 1) (ball 0 R)
  have hr : (fun x => D.realGradient x 0) =ᵐ[volume.restrict (ball 0 R)] fun _ => 1 :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq isOpen_ball hwR (weak_coordinate_one 0 R)
      ((D.real_memLp R 0).locallyIntegrable (by norm_num)) (locallyIntegrable_const 1)
  have hi : (fun x => D.imagGradient x 1) =ᵐ[volume.restrict (ball 0 R)] fun _ => 1 :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq isOpen_ball hwI (weak_coordinate_one 1 R)
      ((D.imag_memLp R 1).locallyIntegrable (by norm_num)) (locallyIntegrable_const 1)
  have hnull : ∀ᵐ x ∂volume, x ∉ K := by
    have hr' := (ae_restrict_iff' measurableSet_ball).mp hr
    have hi' := (ae_restrict_iff' measurableSet_ball).mp hi
    filter_upwards [hsys,hr',hi'] with x hx hxr hxi hxK
    have he := hx.1
    rw [hxr (hKR hxK),hxi (hKR hxK)] at he
    have hv : conductivityValue K 2 x = 2 := by simp [conductivityValue,hxK]
    rw [hv] at he
    norm_num at he
  simpa only [not_not,Set.ofPred_mem_eq] using (ae_iff.mp hnull)

 theorem removable_complement_volume_zero
    (hprincipal : PrincipalRealBeltrami) {G : Set Sphere}
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hrem : IsConformallyRemovable Gᶜ) :
    volume (physicalPlaneDomain G)ᶜ = 0 := by
  have hno : OnePoint.infty ∉ Gᶜ := fun h => h hinf
  have hK := hG.isClosed_compl.isCompact.image_of_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty hno)
  have heq : complexPlaneCoordinates.symm '' (finiteCoord '' Gᶜ) =
      (physicalPlaneDomain G)ᶜ := by
    ext x
    constructor
    · rintro ⟨z,⟨p,hp,rfl⟩,rfl⟩
      change (complexPlaneCoordinates (complexPlaneCoordinates.symm (finiteCoord p)) : Sphere) ∉ G
      rw [complexPlaneCoordinates.apply_symm_apply]
      have hc : ((finiteCoord p : ℂ) : Sphere) = p :=
        CannonMobius.coe_coordinate (fun he => hno (he ▸ hp))
      rwa [hc]
    · intro hx
      exact ⟨complexPlaneCoordinates x,⟨planeSphere x,hx,rfl⟩,
        complexPlaneCoordinates.symm_apply_apply x⟩
  have hcompact : IsCompact (physicalPlaneDomain G)ᶜ := by
    rw [← heq]
    exact hK.image complexPlaneCoordinates.symm.continuous
  have himage : planeSphere '' (physicalPlaneDomain G)ᶜ = Gᶜ := by
    ext p
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hp
      obtain ⟨x,rfl⟩ := exists_planeSphere_eq (fun he => hno (he ▸ hp))
      exact ⟨x,hp,rfl⟩
  apply removable_physical_compact_volume_zero hprincipal hcompact
  rwa [himage]

end CircleDomainRigidity

end

end OAI
