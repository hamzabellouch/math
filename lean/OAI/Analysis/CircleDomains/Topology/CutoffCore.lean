import OAI.Analysis.CircleDomains.Transfer.CoreGeometry

namespace OAI

/-!
# The physical core containing the entire cutoff transition

Taking the complement of the open one-plateau of the cutoff gives a
compact spherical subset of the original domain. Choosing all disk
closures off this larger core guarantees genuine staircase collars.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def realChartDomain (G : Set Sphere) : Set (ℝ × ℝ) :=
  (fun z : ℝ × ℝ => ((Complex.equivRealProdCLM.symm z : ℂ) : Sphere)) ⁻¹' G

theorem isOpen_realChartDomain {G : Set Sphere} (hG : IsOpen G) : IsOpen (realChartDomain G) :=
  hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

theorem isCompact_compl_realChartDomain {G : Set Sphere} (hG : IsOpen G)
    (hinfty : OnePoint.infty ∈ G) : IsCompact (realChartDomain G)ᶜ := by
  have hc := ((OnePoint.isOpen_iff_of_mem hinfty).mp hG).2
  exact Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.mpr hc

theorem sphericalCore_mono {A B : Set (ℝ × ℝ)} (hAB : A ⊆ B) :
    sphericalCore A ⊆ sphericalCore B := by
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact infty_mem_sphericalCore B
  | coe z => exact (coe_mem_sphericalCore B z).mpr (hAB ((coe_mem_sphericalCore A z).mp hx))

def cutoffCore (χ : (ℝ × ℝ) → ℝ) : Set Sphere :=
  sphericalCore (interior {z | χ z = 1})ᶜ

theorem isCompact_cutoffCore (χ : (ℝ × ℝ) → ℝ) : IsCompact (cutoffCore χ) :=
  isCompact_sphericalCore isOpen_interior.isClosed_compl

@[simp] theorem infty_mem_cutoffCore (χ : (ℝ × ℝ) → ℝ) : OnePoint.infty ∈ cutoffCore χ :=
  infty_mem_sphericalCore _

theorem cutoffCore_subset_domain {G : Set Sphere} (hinfty : OnePoint.infty ∈ G)
    (χ : (ℝ × ℝ) → ℝ) (hone : ∀ᶠ z in 𝓝ˢ (realChartDomain G)ᶜ, χ z = 1) :
    cutoffCore χ ⊆ G := by
  apply sphericalCore_subset_domain hinfty
  intro z hz
  by_contra hzG
  have hx : Complex.equivRealProdCLM z ∈ (realChartDomain G)ᶜ := by
    simpa only [realChartDomain, mem_compl_iff, mem_preimage,
      ContinuousLinearEquiv.symm_apply_apply] using hzG
  have hlocal : {x | χ x = 1} ∈ 𝓝 (Complex.equivRealProdCLM z) :=
    hone.filter_mono (nhds_le_nhdsSet hx)
  exact hz (mem_interior_iff_mem_nhds.mpr hlocal)

theorem sphericalCore_subset_cutoffCore {K : Set (ℝ × ℝ)} (χ : (ℝ × ℝ) → ℝ)
    (hzero : ∀ᶠ z in 𝓝ˢ K, χ z = 0) : sphericalCore K ⊆ cutoffCore χ := by
  apply sphericalCore_mono
  intro z hz hzplateau
  have h1 : χ z = 1 := (interior_subset : interior {x | χ x = 1} ⊆ {x | χ x = 1}) hzplateau
  have h0 := hzero.self_of_nhdsSet z hz
  linarith

/-- A filling closure off the cutoff core has its whole boundary in
the open region where the modification is exactly the staircase. -/
theorem boundary_in_one_plateau_of_disjoint_cutoffCore
    (H : ℂ ≃ₜ ℂ) (χ : (ℝ × ℝ) → ℝ)
    (hdisj : Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior H)) (cutoffCore χ)) :
    ∀ z ∈ frontier (jordanInterior H), Complex.equivRealProdCLM z ∈ interior {x | χ x = 1} := by
  intro z hz
  by_contra hnot
  exact Set.disjoint_left.mp hdisj ⟨z, frontier_subset_closure hz, rfl⟩
    ((coe_mem_sphericalCore _ z).mpr hnot)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
