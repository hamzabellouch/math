import OAI.AlgebraicTopology.IntegralHomology.Compactification
import OAI.AlgebraicTopology.IntegralHomology.MayerVietoris
import OAI.AlgebraicTopology.IntegralHomology.Product
import OAI.AlgebraicTopology.IntegralHomology.ProjectiveClass

namespace OAI

noncomputable section

namespace Kaplansky

/-! Hyperplane bundle charts, local-global comparison, and fiber normalization. -/

section
open Bundle Topology
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

abbrev canonicalBundleChartDomain :=
  {z : TotalSpace (hyperplaneProductStage K).Model (hyperplaneProductStage K).Fiber |
    z.proj ∈ (canonicalProductGraphChart K).source}

theorem canonical_chartBaseMap_eq (A : ProjectiveProductModel K) :
    chartBaseMap (canonicalProductGraphChart K).source
      (canonicalProductChartHomeomorph K) A = canonicalProductGraphPoint K A := rfl

def canonicalGraphProjection (s : Σ i, Fin (K i)) :
    C(ProjectiveProductModel K, projectionSpace (1+K s.1) 1) :=
  (projectiveProjectionMap (K s.1)).comp
    ((⟨fun P : ProjectiveProduct K => P s.1, continuous_apply s.1⟩ :
      C(ProjectiveProduct K, Grassmann 1 (K s.1))).comp
      (chartBaseMap (canonicalProductGraphChart K).source (canonicalProductChartHomeomorph K)))

theorem canonicalGraphProjection_eq (s : Σ i, Fin (K i)) (A : ProjectiveProductModel K) :
    canonicalGraphProjection K s A =
      graphLineProjection (standardLineGraphFrame (K s.1)) (A s.1) :=
  projectiveProjectionEquiv_symm_slopePoint _ _

def canonicalGraphVector (s : Σ i, Fin (K i)) (A : ProjectiveProductModel K) :=
  graphLineVector (standardLineGraphFrame (K s.1)) (A s.1)

theorem canonicalGraphVector_mem (s : Σ i, Fin (K i)) (A : ProjectiveProductModel K) :
    canonicalGraphVector K s A ∈ projectionLine (canonicalGraphProjection K s A) := by
  rw [canonicalGraphProjection_eq]
  exact graphLineVector_mem _ _

omit [Fintype ι] in
theorem canonicalGraphVector_ne_zero (s : Σ i, Fin (K i)) (A : ProjectiveProductModel K) :
    canonicalGraphVector K s A ≠ 0 := graphLineVector_ne_zero _ _

omit [Fintype ι] in
theorem continuous_canonicalGraphVector (s : Σ i, Fin (K i)) :
    Continuous (canonicalGraphVector K s) :=
  (continuous_graphLineVector _).comp (continuous_apply s.1)

/-- Actual bundle coordinates on the inverse image of the canonical base
chart. This is a homeomorphism of the original total-space subspace. -/
def canonicalBundleChartHomeomorph : canonicalBundleChartDomain K ≃ₜ
    ProjectiveProductModel K × ((Σ i, Fin (K i)) → ℂ) :=
  (lineSumChartPullbackHomeomorph
    (fun s : Σ i, Fin (K i) => productLineCore K (some s.1))
    (canonicalProductGraphChart K).source (canonicalProductChartHomeomorph K)).symm.trans
    (finiteLineEvaluationHomeomorph (canonicalGraphProjection K) (canonicalGraphVector K)
      (canonicalGraphVector_mem K) (canonicalGraphVector_ne_zero K)
      (continuous_canonicalGraphVector K))

theorem canonicalBundleChartHomeomorph_base (z : canonicalBundleChartDomain K) :
    (canonicalBundleChartHomeomorph K z).1 =
      canonicalProductChartHomeomorph K ⟨z.1.proj,z.2⟩ := rfl

theorem canonicalBundleChartHomeomorph_zero_iff (z : canonicalBundleChartDomain K) :
    (canonicalBundleChartHomeomorph K z).2 = 0 ↔ z.1.2 = 0 :=
  (finiteLineEvaluationEquiv (canonicalGraphProjection K) (canonicalGraphVector K)
    (canonicalGraphVector_mem K) (canonicalGraphVector_ne_zero K) _).map_eq_zero_iff

/-- The restriction of the actual section, before applying bundle coordinates. -/
def canonicalRestrictedSection : C((canonicalProductGraphChart K).source, canonicalBundleChartDomain K) :=
  ⟨fun P => ⟨⟨P.1,hyperplaneProductSection K P.1⟩,P.2⟩,
    ((continuous_hyperplaneProductSection K).comp continuous_subtype_val).subtype_mk _⟩

theorem canonicalBundleChartHomeomorph_section (P : (canonicalProductGraphChart K).source) :
    canonicalBundleChartHomeomorph K (canonicalRestrictedSection K P) =
      (canonicalProductChartHomeomorph K P,canonicalLocalSectionMap K P) := by
  apply Prod.ext
  · rfl
  let A := canonicalProductChartHomeomorph K P
  have hP : P.1 = canonicalProductGraphPoint K A := by
    change P.1 = chartBaseMap (canonicalProductGraphChart K).source (canonicalProductChartHomeomorph K) A
    change P.1 = ((canonicalProductChartHomeomorph K).symm
      (canonicalProductChartHomeomorph K P)).val
    rw [Homeomorph.symm_apply_apply]
  change finiteLineEvaluationEquiv (canonicalGraphProjection K) (canonicalGraphVector K)
      (canonicalGraphVector_mem K) (canonicalGraphVector_ne_zero K) A
      (hyperplaneProductSection K P.1) = canonicalLocalSectionMap K P
  rw [hP]
  funext s
  change projectionDualLineFiberEquiv (canonicalGraphProjection K s A)
    (hyperplaneProductLineSection K s (canonicalProductGraphPoint K A))
    ⟨canonicalGraphVector K s A,canonicalGraphVector_mem K s A⟩ = _
  change projectionDualLineFiberEquiv (canonicalGraphProjection K s A)
    (hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate (K s.1) s.2))
      (canonicalGraphProjection K s A))
    ⟨canonicalGraphVector K s A,canonicalGraphVector_mem K s A⟩ = _
  rw [hyperplaneFunctionalSection_realization]
  change coordinateFunctional (positiveCoordinate (K s.1) s.2)
    (graphLineVector (standardLineGraphFrame (K s.1)) (A s.1)) =
    canonicalProductSectionCoordinates K A s
  rw [← standard_verticalFunctional, graphVerticalFunctional_vector]
  exact (congrFun (canonicalProductSectionCoordinates_eq K A) s).symm

end

section
open Bundle Topology CategoryTheory
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

def canonicalBundleChartNonzero : Set (canonicalBundleChartDomain K) := {z | z.1.2 ≠ 0}

/-- Normalization of the genuine target over the canonical contractible
chart. It is obtained from actual bundle evaluation and product projection. -/
def canonicalBundleChartFiberIso (n : ℕ) :
    relativeSingularHomology (subspaceInclusion (canonicalBundleChartNonzero K)) n ≅
      relativeSingularHomology
        (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ))) n :=
  relativeHomologyHomeomorphIso (canonicalBundleChartHomeomorph K)
    (canonicalBundleChartNonzero K) {z | z.2 ≠ 0}
    (fun z => (not_congr (canonicalBundleChartHomeomorph_zero_iff K z)).symm) n ≪≫
  productPairProjectionIso (B := ProjectiveProductModel K) ({0}ᶜ) n

theorem canonicalRestrictedSection_mapsTo_nonzero :
    Set.MapsTo (canonicalRestrictedSection K)
      ({⟨firstCoordinateProduct K,canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source) (canonicalBundleChartNonzero K) := by
  intro P hP hz
  exact hP (Subtype.ext ((hyperplaneProductSection_eq_zero_iff K P.1).mp hz))

def canonicalRestrictedSectionRelativeMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({⟨firstCoordinateProduct K,canonicalProduct_zero_in_chart K⟩}ᶜ :
      Set (canonicalProductGraphChart K).source))
    (subspaceInclusion (canonicalBundleChartNonzero K))
    (subspaceMap _ _ (canonicalRestrictedSection K) (canonicalRestrictedSection_mapsTo_nonzero K))
    (TopCat.ofHom (canonicalRestrictedSection K)) (by rfl) n

/-- Compatibility of the ACTUAL restricted section with the preserved
local coordinate homology isomorphism. This is not just a derivative sign. -/
theorem canonicalRestrictedSectionRelativeMap_normalization (n : ℕ) :
    canonicalRestrictedSectionRelativeMap K n ≫ (canonicalBundleChartFiberIso K n).hom =
      (canonicalLocalRelativeHomologyIso K n).hom := by
  unfold canonicalBundleChartFiberIso
  erw [Iso.trans_hom, ← Category.assoc, relativeHomologyHomeomorphIso_hom]
  change (relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n) ≫
    relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
  unfold canonicalLocalRelativeHomologyIso
  erw [relativeHomologyHomeomorphIso_hom]
  apply relativeHomologyMap_congr_ambient
  ext P : 1
  change (canonicalBundleChartHomeomorph K (canonicalRestrictedSection K P)).2 =
    canonicalLocalSectionHomeomorph K P
  rw [canonicalBundleChartHomeomorph_section]
  exact canonicalLocalSectionMap_eq K P

/-- The actual section induces an isomorphism to the bundle relative
homology OVER THIS CHART in every degree. Global inclusion is separate. -/
theorem canonicalRestrictedSectionRelativeMap_isIso (n : ℕ) :
    IsIso (canonicalRestrictedSectionRelativeMap K n) := by
  have : IsIso (canonicalRestrictedSectionRelativeMap K n ≫
      (canonicalBundleChartFiberIso K n).hom) := by
    rw [canonicalRestrictedSectionRelativeMap_normalization]
    infer_instance
  exact IsIso.of_isIso_comp_right (canonicalRestrictedSectionRelativeMap K n)
    (canonicalBundleChartFiberIso K n).hom

def canonicalRestrictedSectionRelativeIso (n : ℕ) :=
  @asIso _ _ _ _ (canonicalRestrictedSectionRelativeMap K n)
    (canonicalRestrictedSectionRelativeMap_isIso K n)

/-- Top relative homology over the actual bundle chart is ℤ, normalized
using precisely the incoming recursive local generator. -/
def canonicalBundleChartTopHomologyIso (hp : 0 < ∑ i, K i) :
    relativeSingularHomology (subspaceInclusion (canonicalBundleChartNonzero K))
      (2*(∑ i, K i)) ≅ ModuleCat.of ℤ ℤ :=
  (canonicalRestrictedSectionRelativeIso K (2*(∑ i, K i))).symm ≪≫
    canonicalChartExcisionIso K (2*(∑ i, K i)) ≪≫ canonicalProductLocalHomologyIso K hp

def canonicalBundleChartGenerator (hp : 0 < ∑ i, K i) :
    relativeSingularHomology (subspaceInclusion (canonicalBundleChartNonzero K)) (2*(∑ i, K i)) :=
  canonicalRestrictedSectionRelativeMap K (2*(∑ i, K i))
    ((canonicalChartExcisionIso K (2*(∑ i, K i))).inv (canonicalProductLocalGenerator K hp))

theorem canonicalBundleChartGenerator_coordinate (hp : 0 < ∑ i, K i) :
    (canonicalBundleChartTopHomologyIso K hp).hom (canonicalBundleChartGenerator K hp) = (1 : ℤ) := by
  change (canonicalProductLocalHomologyIso K hp).hom
    ((canonicalChartExcisionIso K _).hom
      ((canonicalRestrictedSectionRelativeIso K _).inv
        ((canonicalRestrictedSectionRelativeIso K _).hom _))) = 1
  simp only [Iso.hom_inv_id_apply, Iso.inv_hom_id_apply]
  exact canonicalProductLocalGenerator_coordinate K hp

theorem canonicalBundleChartGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalBundleChartGenerator K hp ≠ 0 := by
  intro hz
  have h := canonicalBundleChartGenerator_coordinate K hp
  rw [hz,map_zero] at h
  exact Int.zero_ne_one h

/-- Actual inclusion of the bundle over the canonical chart into the
whole ordinary bundle, always removing the entire respective zero section. -/
def canonicalBundleChartRelativeInclusion (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion (canonicalBundleChartNonzero K))
    (subspaceInclusion (nonzeroBundle (V := (hyperplaneProductStage K).Model)
      (E := (hyperplaneProductStage K).Fiber)))
    (subspaceMap _ _ ⟨Subtype.val,continuous_subtype_val⟩
      (fun z hz => (mem_nonzeroBundle z.1).mpr hz))
    (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) (by rfl) n

theorem canonicalRestrictedSection_global_square (n : ℕ) :
    canonicalRestrictedSectionRelativeMap K n ≫ canonicalBundleChartRelativeInclusion K n =
      canonicalChartRelativeInclusion K n ≫ canonicalProductOrdinaryRelativeMap K n := by
  unfold canonicalRestrictedSectionRelativeMap canonicalBundleChartRelativeInclusion
    canonicalChartRelativeInclusion canonicalProductOrdinaryRelativeMap
  erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

theorem canonicalBundleChartGenerator_global_image (hp : 0 < ∑ i, K i) :
    canonicalBundleChartRelativeInclusion K (2*(∑ i, K i))
      (canonicalBundleChartGenerator K hp) =
    canonicalProductOrdinaryRelativeMap K (2*(∑ i, K i))
      (canonicalProductLocalGenerator K hp) := by
  change (canonicalRestrictedSectionRelativeMap K _ ≫ canonicalBundleChartRelativeInclusion K _)
    ((canonicalChartExcisionIso K _).inv _) = _
  rw [canonicalRestrictedSection_global_square]
  change canonicalProductOrdinaryRelativeMap K _
    ((canonicalChartExcisionIso K _).hom ((canonicalChartExcisionIso K _).inv _)) = _
  exact congrArg (canonicalProductOrdinaryRelativeMap K _)
    ((canonicalChartExcisionIso K _).inv_hom_id_apply _)

/-- The same equality in the exact incoming compactified target pair. -/
theorem canonicalBundleChartGenerator_compactified_image (hp : 0 < ∑ i, K i) :
    bundleCompactificationRelativeMap (V := (hyperplaneProductStage K).Model)
      (E := (hyperplaneProductStage K).Fiber) (2*(∑ i, K i))
      (canonicalBundleChartRelativeInclusion K (2*(∑ i, K i))
        (canonicalBundleChartGenerator K hp)) =
    canonicalProductRelativeHomologyMap K (2*(∑ i, K i))
      (canonicalProductLocalGenerator K hp) := by
  rw [canonicalBundleChartGenerator_global_image]
  exact ConcreteCategory.congr_hom (canonicalProductRelativeMap_compactification K _) _

/-- Evaluation of the actual global section on the preserved fundamental
class, after passing to target relative homology, is this precise chart image. -/
theorem canonicalFundamentalClass_target_image (hp : 0 < ∑ i, K i) :
    absoluteToRelative (subspaceInclusion
      (compactifiedNonzeroBundle (V := (hyperplaneProductStage K).Model)
        (E := (hyperplaneProductStage K).Fiber))) (2*(∑ i, K i))
      (canonicalProductHomologyMap K (2*(∑ i, K i))
        (projectiveProductFundamentalClass K hp)) =
    bundleCompactificationRelativeMap (V := (hyperplaneProductStage K).Model)
      (E := (hyperplaneProductStage K).Fiber) (2*(∑ i, K i))
      (canonicalBundleChartRelativeInclusion K (2*(∑ i, K i))
        (canonicalBundleChartGenerator K hp)) := by
  rw [canonicalBundleChartGenerator_compactified_image]
  have h := ConcreteCategory.congr_hom (canonicalProductRelativeHomology_comparison K
    (2*(∑ i, K i))) (projectiveProductFundamentalClass K hp)
  change canonicalProductRelativeHomologyMap K _
    (absoluteToRelative _ _ (projectiveProductFundamentalClass K hp)) = _ at h
  rw [projectiveProductFundamentalClass_localizes] at h
  exact h.symm

end

section
open Bundle Topology CategoryTheory Limits
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The actual fiber over the canonical point, embedded using the proved
bundle coordinates. Only the base coordinate is fixed. -/
def canonicalChartFiberEmbedding :
    C(((Σ i, Fin (K i)) → ℂ), canonicalBundleChartDomain K) :=
  ⟨fun w => (canonicalBundleChartHomeomorph K).symm (0,w),
    (canonicalBundleChartHomeomorph K).symm.continuous.comp
      (continuous_const.prodMk continuous_id)⟩

theorem canonicalChartFiberEmbedding_base (w : (Σ i, Fin (K i)) → ℂ) :
    (canonicalChartFiberEmbedding K w).1.proj = firstCoordinateProduct K := by
  have h := congrArg Prod.fst ((canonicalBundleChartHomeomorph K).apply_symm_apply (0,w))
  change (canonicalBundleChartHomeomorph K (canonicalChartFiberEmbedding K w)).1 = 0 at h
  rw [canonicalBundleChartHomeomorph_base, ← canonicalProductChartHomeomorph_zero K] at h
  exact congrArg Subtype.val ((canonicalProductChartHomeomorph K).injective h)

theorem canonicalChartFiberEmbedding_mapsTo_nonzero :
    Set.MapsTo (canonicalChartFiberEmbedding K)
      ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)) (canonicalBundleChartNonzero K) := by
  intro w hw hz
  have h := (canonicalBundleChartHomeomorph_zero_iff K (canonicalChartFiberEmbedding K w)).mpr hz
  change ((canonicalBundleChartHomeomorph K)
    ((canonicalBundleChartHomeomorph K).symm (0,w))).2 = 0 at h
  rw [Homeomorph.apply_symm_apply] at h
  exact hw h

def canonicalChartFiberRelativeMap (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)))
    (subspaceInclusion (canonicalBundleChartNonzero K))
    (subspaceMap _ _ (canonicalChartFiberEmbedding K) (canonicalChartFiberEmbedding_mapsTo_nonzero K))
    (TopCat.ofHom (canonicalChartFiberEmbedding K)) (by rfl) n

/-- Fiber inclusion is the inverse of the proved local bundle normalization.
This identifies the normalization geometrically at chain-map level. -/
theorem canonicalChartFiberRelativeMap_normalization (n : ℕ) :
    canonicalChartFiberRelativeMap K n ≫ (canonicalBundleChartFiberIso K n).hom = 𝟙 _ := by
  unfold canonicalBundleChartFiberIso
  erw [Iso.trans_hom, ← Category.assoc, relativeHomologyHomeomorphIso_hom]
  change (relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n) ≫
    relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
  rw [← relativeHomologyMap_id (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ))) n]
  apply relativeHomologyMap_congr_ambient
  ext w : 1
  exact congrArg Prod.snd ((canonicalBundleChartHomeomorph K).apply_symm_apply (0,w))

theorem canonicalChartFiberRelativeMap_eq_inv (n : ℕ) :
    canonicalChartFiberRelativeMap K n = (canonicalBundleChartFiberIso K n).inv := by
  apply (cancel_mono (canonicalBundleChartFiberIso K n).hom).mp
  rw [canonicalChartFiberRelativeMap_normalization, Iso.inv_hom_id]

theorem canonicalChartFiberRelativeMap_isIso (n : ℕ) :
    IsIso (canonicalChartFiberRelativeMap K n) := by
  rw [canonicalChartFiberRelativeMap_eq_inv]
  infer_instance

/-- The preserved recursive local class, now expressed in the actual fiber
coordinate group. Its normalization is transported, never independently chosen. -/
def canonicalFiberGenerator (hp : 0 < ∑ i, K i) :
    relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)))
      (2*(∑ i, K i)) :=
  (canonicalBundleChartFiberIso K (2*(∑ i, K i))).hom (canonicalBundleChartGenerator K hp)

theorem canonicalFiberGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalFiberGenerator K hp ≠ 0 := by
  intro hz
  exact canonicalBundleChartGenerator_ne_zero K hp
    ((ModuleCat.mono_iff_injective (canonicalBundleChartFiberIso K _).hom).mp
      inferInstance (hz.trans (map_zero _).symm))

theorem canonicalFiberGenerator_chart_image (hp : 0 < ∑ i, K i) :
    canonicalChartFiberRelativeMap K (2*(∑ i, K i)) (canonicalFiberGenerator K hp) =
      canonicalBundleChartGenerator K hp := by
  rw [canonicalChartFiberRelativeMap_eq_inv]
  exact (canonicalBundleChartFiberIso K _).hom_inv_id_apply _

/-- Actual inclusion of this one fiber into the ordinary whole-bundle pair. -/
def canonicalWholeBundleFiberMap (n : ℕ) :=
  canonicalChartFiberRelativeMap K n ≫ canonicalBundleChartRelativeInclusion K n

/-- The incoming target obligation is the survival of the preserved class
under inclusion of a single actual fiber. All local comparisons are proved. -/
theorem canonicalFiberGenerator_whole_image (hp : 0 < ∑ i, K i) :
    canonicalWholeBundleFiberMap K (2*(∑ i, K i)) (canonicalFiberGenerator K hp) =
      canonicalProductOrdinaryRelativeMap K (2*(∑ i, K i))
        (canonicalProductLocalGenerator K hp) := by
  change canonicalBundleChartRelativeInclusion K _
    (canonicalChartFiberRelativeMap K _ (canonicalFiberGenerator K hp)) = _
  rw [canonicalFiberGenerator_chart_image, canonicalBundleChartGenerator_global_image]

/-- Homology of the actual chart target pair is concentrated in its fiber
dimension. This includes vanishing in degrees zero and one when p>0. -/
theorem canonicalBundleChartHomology_isZero (hp : 0 < ∑ i, K i) (n : ℕ)
    (hn : n ≠ 2*(∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion (canonicalBundleChartNonzero K)) n) := by
  apply (localVectorHomology_isZero ((Σ i, Fin (K i)) → ℂ) ?_ n ?_).of_iso
    (canonicalBundleChartFiberIso K n)
  · rw [canonicalCoordinateSpace_real_finrank]
    omega
  · rwa [canonicalCoordinateSpace_real_finrank]

theorem canonicalBundleChartGenerator_spans (hp : 0 < ∑ i, K i)
    (z : relativeSingularHomology (subspaceInclusion (canonicalBundleChartNonzero K)) (2*(∑ i, K i))) :
    ((canonicalBundleChartTopHomologyIso K hp).hom z : ℤ) • canonicalBundleChartGenerator K hp = z := by
  apply (ModuleCat.mono_iff_injective (canonicalBundleChartTopHomologyIso K hp).hom).mp inferInstance
  rw [map_zsmul,canonicalBundleChartGenerator_coordinate]
  exact mul_one _

/-- The complement of the entire canonical fiber, an open subset of the
actual hyperplane bundle total space. -/
def canonicalPuncturedBundle :
    Set (TotalSpace (hyperplaneProductStage K).Model (hyperplaneProductStage K).Fiber) :=
  {z | z.proj ≠ firstCoordinateProduct K}

theorem canonicalBundleChartDomain_open : IsOpen (canonicalBundleChartDomain K) :=
  (canonicalProductGraphChart K).open_source.preimage (FiberBundle.continuous_proj _ _)

theorem canonicalPuncturedBundle_open : IsOpen (canonicalPuncturedBundle K) :=
  isClosed_singleton.isOpen_compl.preimage (FiberBundle.continuous_proj _ _)

theorem canonicalBundle_chart_punctured_cover :
    canonicalBundleChartDomain K ∪ canonicalPuncturedBundle K = Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hz : z.proj = firstCoordinateProduct K
  · apply Or.inl
    change z.proj ∈ (canonicalProductGraphChart K).source
    rw [hz]
    exact canonicalProduct_zero_in_chart K
  · exact Or.inr hz

/-- The removed-subspace convention in the general gluing theorem is
identified with the preserved actual chart pair, with identity ambient map. -/
def canonicalBundleCoverChartIso (n : ℕ) :
    relativeSingularHomology (subspaceInclusion (canonicalBundleChartNonzero K)) n ≅
    relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set (canonicalBundleChartDomain K))) n :=
  relativeHomologyHomeomorphIso (Homeomorph.refl _) _ _
    (fun z => (mem_nonzeroBundle z.1).symm) n

theorem canonicalBundleCoverChartIso_inclusion (n : ℕ) :
    (canonicalBundleCoverChartIso K n).hom ≫
      restrictedPairToAmbientHomologyMap (canonicalBundleChartDomain K) nonzeroBundle n =
        canonicalBundleChartRelativeInclusion K n := by
  unfold canonicalBundleCoverChartIso
  erw [relativeHomologyHomeomorphIso_hom]
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- The incoming normalized generator, merely transported to the general
relative-cover convention. No new generator or orientation is chosen. -/
def canonicalBundleCoverGenerator (hp : 0 < ∑ i, K i) :=
  (canonicalBundleCoverChartIso K (2*(∑ i,K i))).hom (canonicalBundleChartGenerator K hp)

theorem canonicalBundleCoverGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalBundleCoverGenerator K hp ≠ 0 := by
  intro hz
  exact canonicalBundleChartGenerator_ne_zero K hp
    ((ModuleCat.mono_iff_injective (canonicalBundleCoverChartIso K _).hom).mp
      inferInstance (hz.trans (map_zero _).symm))

theorem canonicalBundleCoverGenerator_whole_image (hp : 0 < ∑ i, K i) :
    restrictedPairToAmbientHomologyMap (canonicalBundleChartDomain K) nonzeroBundle
      (2*(∑ i,K i)) (canonicalBundleCoverGenerator K hp) =
    canonicalWholeBundleFiberMap K (2*(∑ i,K i)) (canonicalFiberGenerator K hp) := by
  change ((canonicalBundleCoverChartIso K _).hom ≫
    restrictedPairToAmbientHomologyMap _ _ _) (canonicalBundleChartGenerator K hp) = _
  rw [canonicalBundleCoverChartIso_inclusion]
  change _ = canonicalBundleChartRelativeInclusion K _
    (canonicalChartFiberRelativeMap K _ (canonicalFiberGenerator K hp))
  rw [canonicalFiberGenerator_chart_image]

/-- Exact global obstruction to survival, in the actual two-set bundle
cover. Local nonvanishing alone does not exclude this overlap witness. -/
theorem canonicalFiberGenerator_zero_iff_overlap (hp : 0 < ∑ i, K i) :
    canonicalWholeBundleFiberMap K (2*(∑ i,K i)) (canonicalFiberGenerator K hp) = 0 ↔
    ∃ w : relativeSingularHomology (subspaceInclusion
        (Subtype.val ⁻¹' nonzeroBundle :
          Set ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K))) (2*(∑ i,K i)),
      restrictedPairHomologyMap (Set.inter_subset_left :
        canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K ⊆ canonicalBundleChartDomain K)
        nonzeroBundle (2*(∑ i,K i)) w = canonicalBundleCoverGenerator K hp ∧
      restrictedPairHomologyMap (Set.inter_subset_right :
        canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K ⊆ canonicalPuncturedBundle K)
        nonzeroBundle (2*(∑ i,K i)) w = 0 := by
  rw [← canonicalBundleCoverGenerator_whole_image]
  exact relativeOpenCover_left_image_zero_iff _ _ _
    (canonicalBundleChartDomain_open K) (canonicalPuncturedBundle_open K)
    (canonicalBundle_chart_punctured_cover K) _ _

theorem canonicalBundleChart_first_zero_iff (z : canonicalBundleChartDomain K) :
    (canonicalBundleChartHomeomorph K z).1 = 0 ↔ z.1.proj = firstCoordinateProduct K := by
  rw [canonicalBundleChartHomeomorph_base, ← canonicalProductChartHomeomorph_zero K]
  constructor
  · intro h
    exact congrArg Subtype.val ((canonicalProductChartHomeomorph K).injective h)
  · intro h
    exact congrArg (canonicalProductChartHomeomorph K) (Subtype.ext h)

def firstCoordinateSubspaceHomeomorph {B V : Type} [TopologicalSpace B]
    [TopologicalSpace V] (W : Set B) :
    ({z : B × V | z.1 ∈ W} : Set (B × V)) ≃ₜ W × V where
  toFun z := (⟨z.1.1,z.2⟩,z.1.2)
  invFun z := ⟨(z.1.1,z.2),z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

/-- Actual coordinates on the overlap with the punctured bundle. Its base
is punctured Euclidean space, not a contractible base. -/
def canonicalBundleOverlapHomeomorph :
    ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K) ≃ₜ
      ({0}ᶜ : Set (ProjectiveProductModel K)) × ((Σ i, Fin (K i)) → ℂ) :=
  (subspaceSubsetHomeomorph
    (canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K)
    (canonicalBundleChartDomain K) Set.inter_subset_left).symm.trans
    (((canonicalBundleChartHomeomorph K).subtype
      (q := fun z => z.1 ∈ ({0}ᶜ : Set (ProjectiveProductModel K))) (fun z => by
        change (z.1 ∈ canonicalBundleChartDomain K ∧ z.1.proj ≠ firstCoordinateProduct K) ↔
          (canonicalBundleChartHomeomorph K z).1 ≠ 0
        exact ⟨fun h hz => h.2 ((canonicalBundleChart_first_zero_iff K z).mp hz),
          fun h => ⟨z.2,fun hz => h ((canonicalBundleChart_first_zero_iff K z).mpr hz)⟩⟩)).trans
      (firstCoordinateSubspaceHomeomorph ({0}ᶜ : Set (ProjectiveProductModel K))))

theorem canonicalBundleOverlapHomeomorph_fiber
    (z : ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K)) :
    (canonicalBundleOverlapHomeomorph K z).2 =
      (canonicalBundleChartHomeomorph K ⟨z.1,z.2.1⟩).2 := rfl

theorem canonicalBundleOverlapHomeomorph_nonzero_iff
    (z : ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K)) :
    z.1 ∈ nonzeroBundle ↔ (canonicalBundleOverlapHomeomorph K z).2 ≠ 0 := by
  exact (mem_nonzeroBundle z.1).trans
    (not_congr (canonicalBundleChartHomeomorph_zero_iff K ⟨z.1,z.2.1⟩)).symm

/-- A pair homeomorphism, retaining both the punctured base and the
punctured fiber. This supplies no unjustified projection isomorphism. -/
def canonicalBundleOverlapRelativeIso (n : ℕ) :
    relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle :
        Set ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K))) n ≅
    relativeSingularHomology (subspaceInclusion
      {z : ({0}ᶜ : Set (ProjectiveProductModel K)) × ((Σ i, Fin (K i)) → ℂ) | z.2 ≠ 0}) n :=
  relativeHomologyHomeomorphIso (canonicalBundleOverlapHomeomorph K) _ _
    (canonicalBundleOverlapHomeomorph_nonzero_iff K) n

/-- The overlap-to-chart map followed by chart normalization is exactly
projection to the fiber in these genuine product coordinates. -/
theorem canonicalBundleOverlap_fiber_comparison (n : ℕ) :
    restrictedPairHomologyMap (Set.inter_subset_left :
      canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K ⊆ canonicalBundleChartDomain K)
      nonzeroBundle n ≫ (canonicalBundleCoverChartIso K n).inv ≫
        (canonicalBundleChartFiberIso K n).hom =
    (canonicalBundleOverlapRelativeIso K n).hom ≫
      productPairProjection (B := ({0}ᶜ : Set (ProjectiveProductModel K)))
        ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)) n := by
  let f : C(↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K),
      canonicalBundleChartDomain K) :=
    ⟨fun z => ⟨z.1,z.2.1⟩,continuous_subtype_val.subtype_mk _⟩
  let j := relativeHomologyMap (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle :
        Set ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K)))
    (subspaceInclusion (canonicalBundleChartNonzero K))
    (subspaceMap _ _ f (fun z hz => (mem_nonzeroBundle z.1).mp hz))
    (TopCat.ofHom f) (by rfl) n
  have hj : j ≫ (canonicalBundleCoverChartIso K n).hom =
      restrictedPairHomologyMap (Set.inter_subset_left :
        canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K ⊆ canonicalBundleChartDomain K)
        nonzeroBundle n := by
    unfold canonicalBundleCoverChartIso
    erw [relativeHomologyHomeomorphIso_hom]
    change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
    erw [relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    rfl
  rw [← hj, Category.assoc, Iso.hom_inv_id_assoc]
  exact productPairNormalization_restrict _ _ f (fun z hz => (mem_nonzeroBundle z.1).mp hz)
    (canonicalBundleOverlapHomeomorph K) (canonicalBundleChartHomeomorph K)
    (canonicalBundleOverlapHomeomorph_nonzero_iff K)
    (fun z => (not_congr (canonicalBundleChartHomeomorph_zero_iff K z)).symm)
    (fun _ => rfl) n

end

open Bundle Topology CategoryTheory Limits
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

def canonicalBundleCoverTopHomologyIso (hp : 0 < ∑ i, K i) :
    relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set (canonicalBundleChartDomain K))) (2*(∑ i,K i)) ≅
      ModuleCat.of ℤ ℤ :=
  (canonicalBundleCoverChartIso K (2*(∑ i,K i))).symm ≪≫
    canonicalBundleChartTopHomologyIso K hp

theorem canonicalBundleCoverGenerator_coordinate (hp : 0 < ∑ i, K i) :
    (canonicalBundleCoverTopHomologyIso K hp).hom (canonicalBundleCoverGenerator K hp) = (1 : ℤ) := by
  change (canonicalBundleChartTopHomologyIso K hp).hom
    ((canonicalBundleCoverChartIso K _).inv
      ((canonicalBundleCoverChartIso K _).hom (canonicalBundleChartGenerator K hp))) = _
  rw [Iso.hom_inv_id_apply, canonicalBundleChartGenerator_coordinate]

def canonicalOverlapChartMap (n : ℕ) :=
  restrictedPairHomologyMap (Set.inter_subset_left :
    canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K ⊆ canonicalBundleChartDomain K)
    nonzeroBundle n

def canonicalOverlapPuncturedMap (n : ℕ) :=
  restrictedPairHomologyMap (Set.inter_subset_right :
    canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K ⊆ canonicalPuncturedBundle K)
    nonzeroBundle n

/-- The preserved integer normalization measured through the actual
overlap-to-chart map. It is not a global Thom class. -/
def canonicalOverlapNormalization (hp : 0 < ∑ i, K i) :=
  canonicalOverlapChartMap K (2*(∑ i,K i)) ≫ (canonicalBundleCoverTopHomologyIso K hp).hom

theorem canonicalOverlap_normalization_eq_one_iff (hp : 0 < ∑ i, K i)
    (w : relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle :
        Set ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K))) (2*(∑ i,K i))) :
    canonicalOverlapNormalization K hp w = (1 : ℤ) ↔
      canonicalOverlapChartMap K (2*(∑ i,K i)) w = canonicalBundleCoverGenerator K hp := by
  change (canonicalBundleCoverTopHomologyIso K hp).hom
    (canonicalOverlapChartMap K _ w) = (1 : ℤ) ↔ _
  rw [← canonicalBundleCoverGenerator_coordinate K hp]
  exact (ModuleCat.mono_iff_injective (canonicalBundleCoverTopHomologyIso K hp).hom).mp
    inferInstance |>.eq_iff

/-- Exact test for failure of the incoming global survival obligation.
Excluding this normalized overlap witness is still a genuine global problem. -/
theorem canonicalFiberGenerator_zero_iff_normalized_overlap (hp : 0 < ∑ i, K i) :
    canonicalWholeBundleFiberMap K (2*(∑ i,K i)) (canonicalFiberGenerator K hp) = 0 ↔
      ∃ w : relativeSingularHomology (subspaceInclusion
        (Subtype.val ⁻¹' nonzeroBundle :
          Set ↥(canonicalBundleChartDomain K ∩ canonicalPuncturedBundle K))) (2*(∑ i,K i)),
        canonicalOverlapNormalization K hp w = (1 : ℤ) ∧
        canonicalOverlapPuncturedMap K (2*(∑ i,K i)) w = 0 := by
  rw [canonicalFiberGenerator_zero_iff_overlap]
  apply exists_congr
  intro w
  rw [canonicalOverlap_normalization_eq_one_iff]
  rfl

end

end Kaplansky

end

end OAI
