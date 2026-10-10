import OAI.Analysis.CircleDomains.Topology.BoundedSphereHomotopy

namespace OAI

/-! Principal normalization gives bounded displacement on the entire
plane. Its straight-line sphere homotopy supplies the orientation class
used in the definition of conformal removability. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_homeomorph_orientation (H : Sphere ≃ₜ Sphere)
    (hnorm : IsPrincipalNormalized H) : OrientationPreserving H := by
  let F := fun z : ℂ => finiteCoord (H (z : Sphere))
  have hfinite (z : ℂ) : H (z : Sphere) ≠ OnePoint.infty := by
    intro he
    have hh : (z : Sphere) = OnePoint.infty := H.injective (he.trans hnorm.1.symm)
    exact OnePoint.coe_ne_infty z hh
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro z
    have hc : ContinuousAt finiteCoord (H (z : Sphere)) :=
      (continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds (hfinite z))
    have hh : ContinuousAt (fun z : ℂ => H (z : Sphere)) z :=
      (H.continuous.comp OnePoint.continuous_coe).continuousAt
    exact hc.comp_of_eq hh rfl
  have hzero := principal_remainder_tendsto_zero hnorm.2
  have hsmall : ∀ᶠ z in Filter.cocompact ℂ, ‖F z-z‖ ≤ 1 := by
    rw [← Metric.cobounded_eq_cocompact]
    have hn := hzero.norm
    simp only [norm_zero] at hn
    exact (hn.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))).mono (fun _ h => h.le)
  obtain ⟨K,hK,hKout⟩ := Filter.mem_cocompact.mp hsmall
  obtain ⟨R,hR⟩ := (hK.image (hF.sub continuous_id)).isBounded.exists_norm_le
  have hbound (z : ℂ) : ‖F z-z‖ ≤ max R 1 := by
    by_cases hz : z ∈ K
    · exact (hR _ (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    · exact (hKout hz).trans (le_max_right _ _)
  have hExt : extendAtInfinity F = H := by
    funext p
    cases p using OnePoint.rec with
    | infty => exact hnorm.1.symm
    | coe z => exact CannonMobius.coe_coordinate (hfinite z)
  have hh := homotopic_id_of_bounded_displacement hF
    (show (0:ℝ) ≤ max R 1 by exact zero_le_one.trans (le_max_right _ _)) hbound
    (hExt.symm ▸ H.continuous)
  unfold OrientationPreserving
  simpa only [hExt] using hh

end CircleDomainRigidity

end

end OAI
