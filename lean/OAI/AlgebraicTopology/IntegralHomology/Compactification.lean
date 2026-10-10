import OAI.AlgebraicTopology.IntegralHomology.Excision
import OAI.AlgebraicTopology.IntegralHomology.Thom

namespace OAI

noncomputable section

namespace Kaplansky

/-! Compactification excision and ordinary relative section classes. -/

section
open Bundle Topology CategoryTheory OnePoint
variable {B V : Type} {E : B → Type} [∀ b, NormedAddCommGroup (E b)]

/-- The ordinary total space with its entire zero section removed. -/
def nonzeroBundle : Set (TotalSpace V E) :=
  ((↑) : TotalSpace V E → OnePoint (TotalSpace V E)) ⁻¹'
    compactifiedNonzeroBundle

theorem mem_nonzeroBundle (z : TotalSpace V E) : z ∈ nonzeroBundle ↔ z.2 ≠ 0 :=
  coe_mem_compactifiedNonzeroBundle z.proj z.2

variable [TopologicalSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [∀ b, NormedSpace ℂ (E b)] [TopologicalSpace (TotalSpace V E)]
  [FiberBundle V E] [VectorBundle ℂ V E]

def bundleCompactificationRelativeMap (n : ℕ) :
    relativeSingularHomology (subspaceInclusion (nonzeroBundle (V := V) (E := E))) n ⟶
      relativeSingularHomology
        (subspaceInclusion (compactifiedNonzeroBundle (V := V) (E := E))) n :=
  relativeHomologyMap _ _
    (subspaceMap _ _ ⟨OnePoint.some, OnePoint.continuous_coe⟩ (fun _ h => h))
    (TopCat.ofHom ⟨OnePoint.some, OnePoint.continuous_coe⟩) (by rfl) n

/-- Compactness of the base makes the zero section closed even in the
one-point total space. Infinity belongs to the removed open set. -/
theorem isOpen_compactifiedNonzeroBundle [CompactSpace B]
    [T2Space (OnePoint (TotalSpace V E))] :
    IsOpen (compactifiedNonzeroBundle (V := V) (E := E)) := by
  exact (isCompact_range (OnePoint.continuous_coe.comp
    (Bundle.Trivialization.continuous_zeroSection ℂ (F := V) (E := E)))).isClosed.isOpen_compl

/-- Excision removes infinity from the actual target pair, in every degree.
The whole zero section stays in the pair throughout. -/
theorem bundleCompactificationRelativeMap_isIso [CompactSpace B]
    [T2Space (OnePoint (TotalSpace V E))] (n : ℕ) :
    IsIso (bundleCompactificationRelativeMap (V := V) (E := E) n) := by
  apply openEmbedding_relativeHomologyMap_isIso
    ⟨OnePoint.some, OnePoint.continuous_coe⟩ OnePoint.isOpenEmbedding_coe _
    isOpen_compactifiedNonzeroBundle
  ext z
  induction z using OnePoint.rec with
  | infty => exact ⟨fun _ => trivial, fun _ => Or.inr infty_mem_compactifiedNonzeroBundle⟩
  | coe x => exact ⟨fun _ => trivial, fun _ => Or.inl ⟨x,rfl⟩⟩

def bundleCompactificationRelativeIso [CompactSpace B]
    [T2Space (OnePoint (TotalSpace V E))] (n : ℕ) :=
  @asIso _ _ _ _ (bundleCompactificationRelativeMap (V := V) (E := E) n)
    (bundleCompactificationRelativeMap_isIso n)

end

section
open Bundle Topology CategoryTheory
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

def canonicalProductOrdinaryRelativeMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)))
    (subspaceInclusion (nonzeroBundle (V := (hyperplaneProductStage K).Model)
      (E := (hyperplaneProductStage K).Fiber)))
    (subspaceMap _ _ ⟨_,continuous_hyperplaneProductSection K⟩ (by
      intro P hP
      exact (mem_nonzeroBundle _).mpr
        (fun hz => hP ((hyperplaneProductSection_eq_zero_iff K P).mp hz))))
    (TopCat.ofHom ⟨_,continuous_hyperplaneProductSection K⟩) (by rfl) n

theorem canonicalProductRelativeMap_compactification (n : ℕ) :
    canonicalProductOrdinaryRelativeMap K n ≫
      bundleCompactificationRelativeMap (V := (hyperplaneProductStage K).Model)
        (E := (hyperplaneProductStage K).Fiber) n = canonicalProductRelativeHomologyMap K n := by
  unfold canonicalProductOrdinaryRelativeMap bundleCompactificationRelativeMap
  erw [relativeHomologyMap_comp]
  rfl

theorem canonicalProductRelativeMap_zero_iff (n : ℕ)
    (z : relativeSingularHomology (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) n) :
    canonicalProductRelativeHomologyMap K n z = 0 ↔
      canonicalProductOrdinaryRelativeMap K n z = 0 := by
  have := @bundleCompactificationRelativeMap_isIso _ (hyperplaneProductStage K).Model
    (hyperplaneProductStage K).Fiber _ _ _ _ _ _
    (smoothLineSumCore K (hyperplaneProductStage K).label).fiberBundle
    (smoothLineSumCore K (hyperplaneProductStage K).label).vectorBundle _ _ n
  rw [← canonicalProductRelativeMap_compactification]
  change bundleCompactificationRelativeMap n (canonicalProductOrdinaryRelativeMap K n z) = 0 ↔ _
  exact ⟨fun h => (ModuleCat.mono_iff_injective (bundleCompactificationRelativeMap n)).mp
    inferInstance (h.trans (map_zero _).symm), fun h => by rw [h,map_zero]⟩

end

open Bundle Topology CategoryTheory
section
variable {B V : Type} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : B → Type} [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℂ (E b)]
  [TopologicalSpace (TotalSpace V E)] [FiberBundle V E] [VectorBundle ℂ V E]

/-- The section's absolute class followed by localization away from the
whole zero section, in the original total space. -/
def ordinarySectionClassMap (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b))) (n : ℕ) :=
  (integralSingularHomology n).map (TopCat.ofHom ⟨_,hs⟩) ≫
    absoluteToRelative (subspaceInclusion (nonzeroBundle (V := V) (E := E))) n

theorem ordinarySectionClassMap_eq (s t : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' V b (t b))) (n : ℕ) :
    ordinarySectionClassMap s hs n = ordinarySectionClassMap t ht n := by
  unfold ordinarySectionClassMap
  rw [integralSingularHomology_homotopy (bundleSectionHomotopy s t hs ht) n]
  rfl

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ b, NormedSpace ℂ (E b)]
  [FiberBundle V E] [VectorBundle ℂ V E] in
/-- A nowhere-zero section factors through the removed subspace, so its
localized absolute map is zero in every degree. -/
theorem ordinarySectionClassMap_eq_zero (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (hne : ∀ b, s b ≠ 0) (n : ℕ) : ordinarySectionClassMap s hs n = 0 := by
  let f : C(B,nonzeroBundle (V := V) (E := E)) :=
    ⟨fun b => ⟨⟨b,s b⟩,(mem_nonzeroBundle _).mpr (hne b)⟩,hs.subtype_mk _⟩
  have he : TopCat.ofHom ⟨_,hs⟩ = TopCat.ofHom f ≫
      subspaceInclusion (nonzeroBundle (V := V) (E := E)) := rfl
  unfold ordinarySectionClassMap
  rw [he,Functor.map_comp,Category.assoc,inclusion_absoluteToRelative,Limits.comp_zero]

end

end Kaplansky

end

end OAI
