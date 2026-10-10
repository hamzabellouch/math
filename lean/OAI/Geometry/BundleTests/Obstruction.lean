import OAI.AlgebraicTopology.IntegralHomology.Obstruction
import OAI.Geometry.BundleTests.Normalization

namespace OAI

noncomputable section

/-! Nonvanishing twisted section classes and the stable retained-bundle obstruction. -/

section
open Bundle Topology CategoryTheory Set
namespace Kaplansky
open ComplexGrassmann
private theorem sectionProductNormalization
    {X Y A V : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace V] [Zero V]
    (U : Set X) (W : Set Y) (s : C(X,Y)) (hs : MapsTo s U W)
    (e : Y ≃ₜ A × V) (f : X ≃ₜ V)
    (he : ∀ y, y ∈ W ↔ (e y).2 ≠ 0) (hf : ∀ x, x ∈ U ↔ f x ∈ ({0}ᶜ : Set V))
    (hcoords : ∀ x, (e (s x)).2 = f x) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion W)
        (subspaceMap U W s hs) (TopCat.ofHom s) (subspaceMap_square U W s hs) n ≫
      ((relativeHomologyHomeomorphIso e W {z | z.2 ≠ 0} he n).hom ≫
        productPairProjection (B := A) ({0}ᶜ : Set V) n) =
      (relativeHomologyHomeomorphIso f U ({0}ᶜ : Set V) hf n).hom := by
  simp only [relativeHomologyHomeomorphIso_hom]
  unfold productPairProjection
  erw [← Category.assoc, relativeHomologyMap_comp, relativeHomologyMap_comp]
  exact relativeHomologyMap_congr_ambient _ _ _ _ _ _ _ _ (by
    ext x : 1
    exact hcoords x) n

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedRestrictedSection : C((twistedStandardChart K h).source,
    twistedGraphBundleDomain K h (twistedStandardChart K h).source) :=
  ⟨fun P => ⟨⟨P.1,twistedHyperplaneSection K h P.1⟩,P.2⟩,
    ((continuous_twistedHyperplaneSection K h).comp continuous_subtype_val).subtype_mk _⟩

theorem twistedStandardBundleCoordinates_section (P : (twistedStandardChart K h).source) :
    twistedGraphBundleCoordinates K h (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl
      (twistedRestrictedSection K h P) =
    (twistedStandardChartHomeomorph K h P,
      twistedSlopeEvaluationEquiv K h (twistedStandardChartHomeomorph K h P)) := by
  apply Prod.ext
  · rfl
  let A := twistedStandardChartHomeomorph K h P
  have hP : P.1 = canonicalProductGraphPoint (twistedProjectiveDimensions K h) A := by
    change P.1 = ((twistedStandardChartHomeomorph K h).symm
      (twistedStandardChartHomeomorph K h P)).val
    rw [Homeomorph.symm_apply_apply]
  change (fun s => (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
    twistedHyperplaneSection K h P.1) s / (show ℂ from twistedStandardLineUnit K h s A)) = _
  rw [hP]
  exact twistedStandardSectionCoordinates_eq K h A

def twistedLocalSectionHomeomorph : (twistedStandardChart K h).source ≃ₜ
    (TwistedHyperplaneSlot K h → ℂ) :=
  (twistedStandardChartHomeomorph K h).trans (twistedSlopeEvaluationEquiv K h).toHomeomorph

theorem twistedLocalSectionHomeomorph_zero :
    twistedLocalSectionHomeomorph K h
      ⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
        canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩ = 0 := by
  change twistedSlopeEvaluationEquiv K h (canonicalProductChartHomeomorph _ _) = 0
  rw [canonicalProductChartHomeomorph_zero,map_zero]

def twistedLocalSectionRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (twistedLocalSectionHomeomorph K h)
    ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ :
      Set (twistedStandardChart K h).source)
    ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) (fun P => by
      change P ≠ _ ↔ twistedLocalSectionHomeomorph K h P ≠ 0
      rw [← twistedLocalSectionHomeomorph_zero K h]
      exact (not_congr (twistedLocalSectionHomeomorph K h).injective.eq_iff).symm) n

def twistedRestrictedSectionRelativeMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ :
      Set (twistedStandardChart K h).source))
    (subspaceInclusion (Subtype.val ⁻¹' nonzeroBundle :
      Set (twistedGraphBundleDomain K h (twistedStandardChart K h).source)))
    (subspaceMap _ _ (twistedRestrictedSection K h) (by
      intro P hP
      exact (mem_nonzeroBundle _).mpr (fun hz => hP
        (Subtype.ext ((twistedHyperplaneSection_eq_zero_iff K h P.1).mp hz)))))
    (TopCat.ofHom (twistedRestrictedSection K h)) (by rfl) n

theorem twistedRestrictedSection_normalization (n : ℕ) :
    twistedRestrictedSectionRelativeMap K h n ≫
      twistedGraphBundleNormalization K h (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl n =
      (twistedLocalSectionRelativeIso K h n).hom := by
  apply sectionProductNormalization
    ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ)
    (Subtype.val ⁻¹' nonzeroBundle) (twistedRestrictedSection K h) _
    (twistedGraphBundleCoordinates K h (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl)
    (twistedLocalSectionHomeomorph K h)
  intro P
  exact congrArg Prod.snd (twistedStandardBundleCoordinates_section K h P)

theorem twistedGraphBundleChartNormalization_isIso
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (n : ℕ) :
    IsIso (twistedGraphBundleChartNormalization K h F n) := by
  let e := twistedGraphBundleRelativeIso K h
    (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source
    (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl n
  let f := productPairProjection (B := ProjectiveProductModel (twistedProjectiveDimensions K h))
    ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n
  change IsIso (e.hom ≫ f)
  exact IsIso.comp_isIso' e.isIso_hom (productPairProjection_isIso _ _)

theorem twistedGraphBundleChartToAmbient_mono
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    Mono (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i))) := by
  obtain ⟨f,hf⟩ := twistedHyperplaneBundle_exists_global_normalization K h F hp
  have : IsIso (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ f) := by
    rw [hf]
    exact twistedGraphBundleChartNormalization_isIso K h F _
  exact mono_of_mono (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
    nonzeroBundle (2*(h+∑ i, K i))) f

theorem twistedProjectiveDimensions_sum :
    ∑ i, twistedProjectiveDimensions K h i = h+∑ i, K i := by
  rw [Fintype.sum_option]
  rfl

def twistedOrdinaryRelativeMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({firstCoordinateProduct (twistedProjectiveDimensions K h)}ᶜ :
      Set (ProjectiveProduct (twistedProjectiveDimensions K h))))
    (subspaceInclusion (nonzeroBundle (V := EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
      (E := (twistedHyperplaneSumCore K h).Fiber)))
    (subspaceMap _ _ ⟨_,continuous_twistedHyperplaneSection K h⟩ (by
      intro P hP
      exact (mem_nonzeroBundle _).mpr
        (fun hz => hP ((twistedHyperplaneSection_eq_zero_iff K h P).mp hz))))
    (TopCat.ofHom ⟨_,continuous_twistedHyperplaneSection K h⟩) (by rfl) n

theorem twistedOrdinaryRelativeMap_chart (n : ℕ) :
    canonicalChartRelativeInclusion (twistedProjectiveDimensions K h) n ≫
      twistedOrdinaryRelativeMap K h n =
    twistedRestrictedSectionRelativeMap K h n ≫
      restrictedPairToAmbientHomologyMap
        (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n := by
  unfold canonicalChartRelativeInclusion twistedOrdinaryRelativeMap twistedRestrictedSectionRelativeMap
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n =
    relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n
  erw [relativeHomologyMap_comp,relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

theorem twistedOrdinaryRelativeMap_mono (hp : 0 < h+∑ i, K i) :
    Mono (twistedOrdinaryRelativeMap K h (2*(h+∑ i, K i))) := by
  let n := 2*(h+∑ i, K i)
  let e := canonicalChartExcisionIso (twistedProjectiveDimensions K h) n
  let r := twistedRestrictedSectionRelativeMap K h n
  let f := twistedGraphBundleNormalization K h (twistedStandardChart K h).source
    (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl n
  have : IsIso (r ≫ f) := by
    change IsIso (twistedRestrictedSectionRelativeMap K h n ≫ _)
    rw [twistedRestrictedSection_normalization]
    infer_instance
  have : Mono r := mono_of_mono r f
  have : Mono (restrictedPairToAmbientHomologyMap
      (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n) :=
    twistedGraphBundleChartToAmbient_mono K h (twistedStandardFrames K h) hp
  have he : twistedOrdinaryRelativeMap K h n = e.inv ≫ r ≫
      restrictedPairToAmbientHomologyMap
        (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc,← Category.assoc,e.hom_inv_id,Category.id_comp]
    exact twistedOrdinaryRelativeMap_chart K h n
  change Mono (twistedOrdinaryRelativeMap K h n)
  rw [he]
  infer_instance

theorem twistedOrdinaryRelativeMap_comparison (n : ℕ) :
    absoluteToRelative (subspaceInclusion
      ({firstCoordinateProduct (twistedProjectiveDimensions K h)}ᶜ :
        Set (ProjectiveProduct (twistedProjectiveDimensions K h)))) n ≫
      twistedOrdinaryRelativeMap K h n =
    ordinarySectionClassMap (twistedHyperplaneSection K h)
      (continuous_twistedHyperplaneSection K h) n :=
  absoluteToRelative_naturality _ _ _ _ _ n

/-- The actual twisted section carries the existing augmented-base
fundamental class to a nonzero ordinary relative class. -/
theorem twistedOrdinarySection_fundamental_ne_zero
    (hp : 0 < ∑ i, twistedProjectiveDimensions K h i) :
    ordinarySectionClassMap (twistedHyperplaneSection K h)
      (continuous_twistedHyperplaneSection K h) (2*∑ i, twistedProjectiveDimensions K h i)
      (projectiveProductFundamentalClass (twistedProjectiveDimensions K h) hp) ≠ 0 := by
  have hp' : 0 < h+∑ i, K i := by rwa [twistedProjectiveDimensions_sum] at hp
  have : Mono (twistedOrdinaryRelativeMap K h (2*∑ i, twistedProjectiveDimensions K h i)) := by
    rw [twistedProjectiveDimensions_sum]
    exact twistedOrdinaryRelativeMap_mono K h hp'
  rw [← twistedOrdinaryRelativeMap_comparison]
  change twistedOrdinaryRelativeMap K h _
    (absoluteToRelative _ _ (projectiveProductFundamentalClass _ hp)) ≠ 0
  rw [projectiveProductFundamentalClass_localizes]
  intro hz
  exact canonicalProductLocalGenerator_ne_zero (twistedProjectiveDimensions K h) hp
    ((ModuleCat.mono_iff_injective (twistedOrdinaryRelativeMap K h _)).mp
      inferInstance (hz.trans (map_zero _).symm))

theorem twistedHyperplane_every_section_has_zero (hp : 0 < h+∑ i, K i)
    (s : ∀ P, (twistedHyperplaneSumCore K h).Fiber P)
    (hs : Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P (s P))) :
    ∃ P, s P = 0 := by
  have hp' : 0 < ∑ i, twistedProjectiveDimensions K h i := by
    rw [twistedProjectiveDimensions_sum]; exact hp
  by_contra hn
  push Not at hn
  have hz := ordinarySectionClassMap_eq_zero s hs hn (2*∑ i, twistedProjectiveDimensions K h i)
  have he := @ordinarySectionClassMap_eq _ (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
    _ _ _ (twistedHyperplaneSumCore K h).Fiber _ _ _
    (twistedHyperplaneSumCore K h).fiberBundle (twistedHyperplaneSumCore K h).vectorBundle
    (twistedHyperplaneSection K h) s (continuous_twistedHyperplaneSection K h) hs
    (2*∑ i, twistedProjectiveDimensions K h i)
  have hz := he.trans hz
  apply twistedOrdinarySection_fundamental_ne_zero K h hp'
  rw [hz]
  rfl

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- The tensor construction contradicts any frame with more vectors than
the displayed trivial rank. The frame need not respect the line summands. -/
theorem twistedSourceStage_no_large_frame {ι : Type} [Fintype ι]
    (K : ι → ℕ) (h d : ℕ) (hp : 0 < h+∑ i, K i) (hd : h < d) :
    IsEmpty (ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) := by
  refine ⟨fun f => ?_⟩
  have hd' : 1+h ≤ d := by omega
  obtain ⟨P,hP⟩ := twistedHyperplane_every_section_has_zero K h hp
    (twistedFrameSection K h f hd') (continuous_twistedFrameSection K h f hd')
  exact twistedFrameSection_ne_zero K h f hd' P hP

def retainedTwistedSlotEquiv (m R : ℕ) :
    TwistedHyperplaneSlot (testProjectiveDimension m R) (retainedTrivialMultiplicity m R) ≃
      RetainedGroupedSlot m R where
  toFun
    | .inl j => ⟨none,j⟩
    | .inr s => ⟨some s.1,s.2⟩
  invFun
    | ⟨none,j⟩ => .inl j
    | ⟨some i,j⟩ => .inr ⟨i,j⟩
  left_inv s := by cases s <;> rfl
  right_inv s := by obtain ⟨i,j⟩ := s; cases i <;> rfl

/-- Exact slot regrouping as an actual unitary bundle isomorphism. -/
def retainedTwistedSourceUnitary (m R : ℕ) :
    UnitaryBundleEquiv
      (twistedSourceStage (testProjectiveDimension m R) (retainedTrivialMultiplicity m R)).Model
      (retainedGroupedStage m R).Model
      (twistedSourceStage (testProjectiveDimension m R) (retainedTrivialMultiplicity m R)).Fiber
      (retainedGroupedStage m R).Fiber :=
  lineSumRelabelUnitary (testProjectiveDimension m R)
    (twistedSourceLabel (testProjectiveDimension m R) (retainedTrivialMultiplicity m R))
    (fun s : RetainedGroupedSlot m R => s.1) (retainedTwistedSlotEquiv m R)
    (fun s => by cases s <;> rfl)

theorem retainedGrouped_no_test_frame {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    IsEmpty (ContinuousOrthonormalStageFrame (retainedGroupedStage m R) (2*m*testRank m R 0)) := by
  have hp := retainedTest_hyperplaneDegree_pos hm hR
  have := twistedSourceStage_no_large_frame (testProjectiveDimension m R)
    (retainedTrivialMultiplicity m R) (2*m*testRank m R 0) (by omega)
    (retainedTrivialMultiplicity_bound hm)
  exact ⟨fun f => isEmptyElim (f.congr (retainedTwistedSourceUnitary m R).symm)⟩

/-- Normalizing an arbitrary independent continuous frame reduces it to
the excluded orthonormal frame; no extra metric premise is required. -/
theorem retainedGrouped_no_independent_test_frame {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    IsEmpty (ContinuousIndependentStageFrame (retainedGroupedStage m R) (2*m*testRank m R 0)) := by
  have := retainedGrouped_no_test_frame hm hR
  exact ⟨fun f => isEmptyElim f.normalize⟩

theorem actualAlgebra_matrix_not_properlyInfinite {m : ℕ} (hm : 0 < m) :
    ¬ ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra) := by
  intro hpi
  obtain ⟨R,hR,⟨f⟩⟩ := properlyInfinite_regrouped_frame hm hpi
  have := retainedGrouped_no_test_frame hm hR
  exact isEmptyElim f

end Kaplansky

end

end OAI
