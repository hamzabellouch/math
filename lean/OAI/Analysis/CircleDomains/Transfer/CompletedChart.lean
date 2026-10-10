import OAI.Analysis.CircleDomains.Topology.CutoffCore
import OAI.Analysis.CircleDomains.Transfer.GeometricCompletion

namespace OAI

/-!
# The actual completed region in the finite real chart

These identifications pass the spherical disk completion to the real
coordinates used by the energy estimates, preserving the original core
and the exact open extension domain.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isClosed_realChartDomain {Q : Set Sphere} (hQ : IsClosed Q) :
    IsClosed (realChartDomain Q) :=
  hQ.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

@[simp] theorem realChartDomain_union (G H : Set Sphere) :
    realChartDomain (G ∪ H) = realChartDomain G ∪ realChartDomain H := rfl

@[simp] theorem realChartDomain_sphericalCore (K : Set (ℝ × ℝ)) :
    realChartDomain (sphericalCore K) = K := by
  ext x
  change ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ sphericalCore K ↔ x ∈ K
  simp only [coe_mem_sphericalCore, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem realChartDomain_sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) :
    realChartDomain (sphericalDiskUnion H) = ⋃ i, realJordanInterior (H i) := by
  ext x
  change ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ sphericalDiskUnion H ↔ _
  rw [coe_mem_sphericalDiskUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, Complex.equivRealProdCLM.symm x, hi,
      Complex.equivRealProdCLM.apply_symm_apply x⟩
  · intro hx
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
    refine ⟨i, ?_⟩
    simpa only [← hzx, ContinuousLinearEquiv.symm_apply_apply] using hz

theorem isClosed_real_completedRegion {I : Type*} (T : I → ℂ ≃ₜ ℂ) :
    IsClosed (realChartDomain (completedRegion T)) :=
  isClosed_realChartDomain (isOpen_sphericalDiskUnion T).isClosed_compl

theorem real_completedRegion_subset_extension
    {I J : Type*} (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion H) :
    realChartDomain (completedRegion T) ⊆ realChartDomain G ∪ ⋃ j, realJordanInterior (H j) := by
  have hsub : realChartDomain (completedRegion T) ⊆ realChartDomain (G ∪ sphericalDiskUnion H) :=
    preimage_mono (completedRegion_subset_extension_domain T H G B π hbad hcover)
  simpa only [realChartDomain_union, realChartDomain_sphericalDiskUnion] using hsub

theorem real_core_avoids_filling
    {J : Type*} {K : Set (ℝ × ℝ)} {C : Set Sphere} (H : J → ℂ ≃ₜ ℂ)
    (hKC : sphericalCore K ⊆ C)
    (hHC : ∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) C) :
    ∀ x ∈ K, ∀ j, x ∉ realJordanInterior (H j) := by
  intro x hx j hj
  obtain ⟨z, hz, rfl⟩ := hj
  exact Set.disjoint_left.mp (hHC j) ⟨z, subset_closure hz, rfl⟩
    (hKC ((coe_mem_sphericalCore K z).mpr hx))

theorem real_boundary_in_domain_and_plateau
    {J : Type*} {G : Set Sphere} (H : J → ℂ ≃ₜ ℂ) (χ : (ℝ × ℝ) → ℝ)
    (hG : ∀ j z, z ∈ frontier (jordanInterior (H j)) → (z : Sphere) ∈ G)
    (hHC : ∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) (cutoffCore χ)) :
    ∀ j z, z ∈ frontier (jordanInterior (H j)) →
      Complex.equivRealProdCLM z ∈ realChartDomain G ∩ interior {x | χ x = 1} := by
  intro j z hz
  refine ⟨?_, boundary_in_one_plateau_of_disjoint_cutoffCore (H j) χ (hHC j) z hz⟩
  simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hG j z hz

end CircleDomainRigidity.FiniteTransfer

end

end OAI
