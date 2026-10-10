import OAI.Analysis.CircleDomains.Selection.PhysicalTerminals
import OAI.Analysis.CircleDomains.Selection.FinitePatching

namespace OAI

/-!
# The retained core and completed domain of a finite disk construction

The core is the spherical complement of all terminal and filling disks.
If the disks cover the preimage of the quotient dust, the core is a compact
subset of the original domain. Filling the second family leaves precisely
the complement of the terminal interiors. This completed compact set has
the open neighborhood consisting of the original domain and the filling
interiors. In a finite chart its bounded closed pieces are compact, even
though the entire planar exterior is unbounded.

The final statements apply the actual finite patching construction to this
open neighborhood and recover local agreement on the retained core.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

def sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i)

def completionCore {I J : Type*} (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ) : Set Sphere :=
  (sphericalDiskUnion T ∪ sphericalDiskUnion F)ᶜ

def completedRegion {I : Type*} (T : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  (sphericalDiskUnion T)ᶜ

theorem isOpen_sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) :
    IsOpen (sphericalDiskUnion H) :=
  isOpen_iUnion fun i => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))

@[simp] theorem coe_mem_sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) (z : ℂ) :
    (z : Sphere) ∈ sphericalDiskUnion H ↔ ∃ i, z ∈ jordanInterior (H i) := by
  simp [sphericalDiskUnion, OnePoint.coe_injective.mem_set_image]

@[simp] theorem infty_not_mem_sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) :
    OnePoint.infty ∉ sphericalDiskUnion H := by
  simp [sphericalDiskUnion]

theorem isCompact_completionCore {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ) : IsCompact (completionCore T F) :=
  ((isOpen_sphericalDiskUnion T).union (isOpen_sphericalDiskUnion F)).isClosed_compl.isCompact

theorem isCompact_completedRegion {I : Type*} (T : I → ℂ ≃ₜ ℂ) :
    IsCompact (completedRegion T) :=
  (isOpen_sphericalDiskUnion T).isClosed_compl.isCompact

/-- Covering the actual preimage of the dust removes every point outside
the original domain. -/
theorem completionCore_subset_domain {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion F) :
    completionCore T F ⊆ G := by
  intro x hx
  by_contra hxG
  exact hx (hcover (hbad x hxG))

theorem disjoint_sphericalDiskUnion_of_closures {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (hTF : ∀ i j, Disjoint (closure (jordanInterior (T i)))
      (closure (jordanInterior (F j)))) :
    Disjoint (sphericalDiskUnion T) (sphericalDiskUnion F) := by
  apply Set.disjoint_left.mpr
  intro x hxT hxF
  cases x using OnePoint.rec with
  | infty => exact infty_not_mem_sphericalDiskUnion T hxT
  | coe z =>
    obtain ⟨i, hi⟩ := (coe_mem_sphericalDiskUnion T z).mp hxT
    obtain ⟨j, hj⟩ := (coe_mem_sphericalDiskUnion F z).mp hxF
    exact Set.disjoint_left.mp (hTF i j) (subset_closure hi) (subset_closure hj)

/-- Filling the second family leaves exactly the complement of the
terminal interiors, including their boundaries. -/
theorem completedRegion_eq_core_union_fillings {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (hTF : ∀ i j, Disjoint (closure (jordanInterior (T i)))
      (closure (jordanInterior (F j)))) :
    completedRegion T = completionCore T F ∪ sphericalDiskUnion F := by
  have hd := disjoint_sphericalDiskUnion_of_closures T F hTF
  ext x
  constructor
  · intro hx
    by_cases hf : x ∈ sphericalDiskUnion F
    · exact Or.inr hf
    · exact Or.inl (fun h => h.elim hx hf)
  · rintro (hx | hx)
    · exact fun h => hx (Or.inl h)
    · exact fun h => Set.disjoint_left.mp hd h hx

/-- Every filling closure is disjoint from the terminal interiors. -/
theorem filling_closure_subset_completedRegion {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (hTF : ∀ i j, Disjoint (closure (jordanInterior (T i)))
      (closure (jordanInterior (F j)))) (j : J) :
    ((↑) : ℂ → Sphere) '' closure (jordanInterior (F j)) ⊆ completedRegion T := by
  rintro _ ⟨z, hz, rfl⟩ hT
  obtain ⟨i, hi⟩ := (coe_mem_sphericalDiskUnion T z).mp hT
  exact Set.disjoint_left.mp (hTF i j) (subset_closure hi) hz

/-- Terminal boundaries in the original domain force whole quotient
fibers to stay on one side, so the union of terminal interiors is saturated. -/
theorem preimage_image_sphericalDiskUnion
    {I : Type*} (T : I → ℂ ≃ₜ ℂ) (G : Set Sphere) (π : Sphere → Sphere)
    (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (T i)) → (z : Sphere) ∈ G) :
    π ⁻¹' (π '' sphericalDiskUnion T) = sphericalDiskUnion T := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, heq⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have hx : x ∈ π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior (T i))) :=
      ⟨y, hi, heq⟩
    rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr (T i)
      (hboundary i)] at hx
    exact mem_iUnion.mpr ⟨i, hx⟩
  · exact subset_preimage_image π _

/-- Filling the quotient dust left after the terminal interiors covers
the complete physical dust preimage. Saturation, rather than just fiber
representative selection, is what makes this implication valid. -/
theorem dust_preimage_covered_of_remainder_cover
    {I J : Type*} (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (T i)) → (z : Sphere) ∈ G)
    (hfill : π ⁻¹' (B \ (π '' sphericalDiskUnion T)) ⊆ sphericalDiskUnion F) :
    π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion F := by
  intro x hxB
  by_cases hxT : π x ∈ π '' sphericalDiskUnion T
  · left
    have hx : x ∈ π ⁻¹' (π '' sphericalDiskUnion T) := hxT
    rwa [preimage_image_sphericalDiskUnion T G π hsurj hr hboundary] at hx
  · exact Or.inr (hfill ⟨hxB, hxT⟩)

/-- A physical finite-chart filling cover supplies the spherical cover
as soon as the quotient remainder omits the infinity fiber. -/
theorem spherical_remainder_cover_of_physical_cover
    {I J : Type*} (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (B : Set Sphere) (π : Sphere → Sphere)
    (hinfty : π OnePoint.infty ∉ B \ (π '' sphericalDiskUnion T))
    (hfill : (fun z : ℂ => π (z : Sphere)) ⁻¹' (B \ (π '' sphericalDiskUnion T)) ⊆
      ⋃ j, jordanInterior (F j)) :
    π ⁻¹' (B \ (π '' sphericalDiskUnion T)) ⊆ sphericalDiskUnion F := by
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact (hinfty hx).elim
  | coe z =>
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hfill hx)
    exact (coe_mem_sphericalDiskUnion F z).mpr ⟨j, hj⟩

/-- No disjointness is needed for this useful containment: every point
left after deleting the terminals is either physical or inside a filling. -/
theorem completedRegion_subset_extension_domain {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion F) :
    completedRegion T ⊆ G ∪ sphericalDiskUnion F := by
  intro x hx
  by_cases hxG : x ∈ G
  · exact Or.inl hxG
  · rcases hcover (hbad x hxG) with hT | hF
    · exact (hx hT).elim
    · exact Or.inr hF

theorem completion_has_open_extension_domain {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (hG : IsOpen G) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion F) :
    IsOpen (G ∪ sphericalDiskUnion F) ∧
      completedRegion T ⊆ G ∪ sphericalDiskUnion F ∧
      G ∪ sphericalDiskUnion F ∈ 𝓝ˢ (completedRegion T) := by
  have ho := hG.union (isOpen_sphericalDiskUnion F)
  have hs := completedRegion_subset_extension_domain T F G B π hbad hcover
  exact ⟨ho, hs, ho.mem_nhdsSet.mpr hs⟩

/-- Direct interface for the actual terminal family and a finite filling
cover of its quotient remainder. No independent total-dust-cover premise
is needed. -/
theorem PhysicalTerminalDisks.completion_geometry
    {I J : Type*} {G B : Set Sphere} {π : Sphere → Sphere}
    {p : I → Sphere} {O : I → Set Sphere}
    (D : PhysicalTerminalDisks G π B p O) (F : J → ℂ ≃ₜ ℂ)
    (hG : IsOpen G) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hfill : π ⁻¹' (B \ (π '' sphericalDiskUnion D.H)) ⊆ sphericalDiskUnion F) :
    IsCompact (completionCore D.H F) ∧ completionCore D.H F ⊆ G ∧
      IsCompact (completedRegion D.H) ∧ IsOpen (G ∪ sphericalDiskUnion F) ∧
      completedRegion D.H ⊆ G ∪ sphericalDiskUnion F := by
  have hcover := dust_preimage_covered_of_remainder_cover D.H F G B π hsurj hr
    (fun i z hz => (D.frontier_good i z hz).1) hfill
  exact ⟨isCompact_completionCore D.H F,
    completionCore_subset_domain D.H F G B π hbad hcover,
    isCompact_completedRegion D.H, hG.union (isOpen_sphericalDiskUnion F),
    completedRegion_subset_extension_domain D.H F G B π hbad hcover⟩

/-- The bounded finite-chart pieces used for local metric selection are
compact and remain in the extension domain. -/
theorem compact_chart_completion_in_extension_domain {I J : Type*}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (G B : Set Sphere) (π : Sphere → Sphere)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hcover : π ⁻¹' B ⊆ sphericalDiskUnion T ∪ sphericalDiskUnion F)
    (c : ℂ) (R : ℝ) :
    IsCompact ((((↑) : ℂ → Sphere) ⁻¹' completedRegion T) ∩ closedBall c R) ∧
      (((↑) : ℂ → Sphere) ⁻¹' completedRegion T) ∩ closedBall c R ⊆
        ((↑) : ℂ → Sphere) ⁻¹' (G ∪ sphericalDiskUnion F) := by
  refine ⟨(isCompact_closedBall c R).of_isClosed_subset ?_ inter_subset_right, ?_⟩
  · exact (((isOpen_sphericalDiskUnion T).isClosed_compl).preimage
      OnePoint.continuous_coe).inter isClosed_closedBall
  · intro z hz
    exact completedRegion_subset_extension_domain T F G B π hbad hcover hz.1

/-- Patching the filling interiors gives smooth coordinates on the
actual open completed domain, not merely on the old physical domain. -/
theorem contDiffOn_finite_completion_patch
    {J : Type*} [Fintype J] (F : J → ℂ ≃ₜ ℂ)
    (hF : Pairwise (Disjoint on fun j => closure (jordanInterior (F j))))
    {G : Set Sphere} (hG : IsOpen G)
    (f : ℂ → ℝ) (hf : ContDiffOn ℝ ∞ f (((↑) : ℂ → Sphere) ⁻¹' G))
    (g : J → ℂ → ℝ) (hg : ∀ j, ContDiffOn ℝ ∞ (g j) (jordanInterior (F j)))
    (hagree : ∀ j z, z ∈ frontier (jordanInterior (F j)) → g j =ᶠ[𝓝 z] f) :
    ContDiffOn ℝ ∞ (patchOpenRegions (fun j => jordanInterior (F j)) g f)
      (((↑) : ℂ → Sphere) ⁻¹' (G ∪ sphericalDiskUnion F)) := by
  apply contDiffOn_patchOpenRegions _ _ _ (fun j => jordanInterior_isOpen (F j))
    (fun i j hij => (hF hij).mono subset_closure subset_closure)
  · intro z hz hn
    rcases hz with hzG | hzF
    · exact hf.contDiffAt ((hG.preimage OnePoint.continuous_coe).mem_nhds hzG)
    · obtain ⟨j, hj⟩ := (coe_mem_sphericalDiskUnion F z).mp hzF
      exact (hn j hj).elim
  · intro j z hz
    exact (hg j).contDiffAt ((jordanInterior_isOpen (F j)).mem_nhds hz.2)
  · intro j z hz
    exact hagree j z hz.2

/-- On the retained core the patched coordinate agrees locally with the
old one, including points on any filling boundary. -/
theorem finite_completion_patch_eq_near_core
    {I J : Type*} [Fintype J] (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (f : ℂ → ℝ) (g : J → ℂ → ℝ)
    (hagree : ∀ j z, z ∈ frontier (jordanInterior (F j)) → g j =ᶠ[𝓝 z] f) :
    patchOpenRegions (fun j => jordanInterior (F j)) g f =ᶠ[
      𝓝ˢ (((↑) : ℂ → Sphere) ⁻¹' completionCore T F)] f := by
  apply eventually_nhdsSet_iff_forall.mpr
  intro z hz
  apply patchOpenRegions_eventuallyEq_outside _ _ _
    (fun j => jordanInterior_isOpen (F j))
  · intro j hj
    exact hz (Or.inr ((coe_mem_sphericalDiskUnion F z).mpr ⟨j, hj⟩))
  · intro j hj
    exact hagree j z hj

end CircleDomainRigidity.FiniteTransfer

end OAI
