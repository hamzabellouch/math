import OAI.AlgebraicTopology.IntegralHomology.Equivalence
import OAI.Geometry.ComplexBundle.Orthonormal
import OAI.Geometry.ComplexBundle.ZeroSign

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative section classes and local homology at hyperplane product zeros. -/

section
open Bundle Topology CategoryTheory OnePoint

section
open ComplexGrassmann
variable {ι : Type} {K : ι → ℕ}

/-- The norm on the actual line-stage total space is continuous. The proof
uses its genuine continuous Hermitian metric, not fixed fiber coordinates. -/
theorem continuous_lineStage_totalNorm (a : LineStage K) :
    Continuous (fun z : TotalSpace a.Model a.Fiber => ‖z.2‖) := by
  have h := continuous_lineStage_inner_over a
    (fun z : TotalSpace a.Model a.Fiber => z.proj) (FiberBundle.continuous_proj _ _)
    (fun z => z.2) (fun z => z.2) continuous_id continuous_id
  convert (Complex.continuous_re.comp h).sqrt using 1
  funext z
  exact norm_eq_sqrt_re_inner (𝕜 := ℂ) z.2

/-- An arbitrary nonempty orthonormal frame forces all section-induced
homology maps of its actual bundle to vanish in positive degree. -/
theorem ContinuousOrthonormalStageFrame.sectionHomologyMap_eq_zero
    {a : LineStage K} {d : ℕ} (f : ContinuousOrthonormalStageFrame a d) (hd : 0 < d)
    (s : ∀ y, a.Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' a.Model y (s y))) {n : ℕ} (hn : n ≠ 0) :
    sectionHomologyMap s hs n = 0 := by
  exact @sectionHomologyMap_eq_zero_of_nonvanishing _ a.Model _ _ _ a.Fiber _ _ _
    (smoothLineSumCore K a.label).fiberBundle (smoothLineSumCore K a.label).vectorBundle
    s (fun y => f.vector y ⟨0,hd⟩)
    hs (f.continuous_vector ⟨0,hd⟩) (continuous_lineStage_totalNorm a)
    (fun y => (f.orthonormal y).ne_zero ⟨0,hd⟩) n hn

variable [Fintype ι]

/-- The actual canonical hyperplane-product section induces this integral
homology morphism. Its nonvanishing still requires a global calculation. -/
def canonicalProductHomologyMap (K : ι → ℕ) (n : ℕ) :=
  sectionHomologyMap (hyperplaneProductSection K) (continuous_hyperplaneProductSection K) n

theorem canonicalProductHomologyMap_eq_section (s : ∀ y, (hyperplaneProductStage K).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' (hyperplaneProductStage K).Model y (s y))) (n : ℕ) :
    canonicalProductHomologyMap K n = sectionHomologyMap s hs n := by
  exact @sectionHomologyMap_eq _ (hyperplaneProductStage K).Model _ _ _
    (hyperplaneProductStage K).Fiber _ _ _
    (smoothLineSumCore K (hyperplaneProductStage K).label).fiberBundle
    (smoothLineSumCore K (hyperplaneProductStage K).label).vectorBundle
    _ _ (continuous_hyperplaneProductSection K) hs n

/-- Applied to the genuine hyperplane sum, a nowhere-zero continuous section
would force the canonical map to vanish. No nonzero-map premise is introduced. -/
theorem canonicalProductHomologyMap_eq_zero_of_nonvanishing
    (s : ∀ y, (hyperplaneProductStage K).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' (hyperplaneProductStage K).Model y (s y)))
    (hne : ∀ y, s y ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    canonicalProductHomologyMap K n = 0 := by
  exact @sectionHomologyMap_eq_zero_of_nonvanishing _ (hyperplaneProductStage K).Model _ _ _
    (hyperplaneProductStage K).Fiber _ _ _
    (smoothLineSumCore K (hyperplaneProductStage K).label).fiberBundle
    (smoothLineSumCore K (hyperplaneProductStage K).label).vectorBundle
    _ s (continuous_hyperplaneProductSection K) hs
    (continuous_lineStage_totalNorm _) hne n hn

theorem canonicalProductHomologyMap_eq_zero_of_frame {d : ℕ}
    (f : ContinuousOrthonormalStageFrame (hyperplaneProductStage K) d) (hd : 0 < d)
    {n : ℕ} (hn : n ≠ 0) : canonicalProductHomologyMap K n = 0 :=
  f.sectionHomologyMap_eq_zero hd _ (continuous_hyperplaneProductSection K) hn

end

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem hyperplaneProduct_nonzeroLocus :
    sectionNonzeroLocus (hyperplaneProductSection K) =
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)) := by
  ext P
  exact not_congr (hyperplaneProductSection_eq_zero_iff K P)

theorem canonicalProduct_mapsTo_nonzero :
    Set.MapsTo (compactifiedSection (hyperplaneProductSection K)
      (continuous_hyperplaneProductSection K))
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))
      (compactifiedNonzeroBundle (V := (hyperplaneProductStage K).Model)
        (E := (hyperplaneProductStage K).Fiber)) := by
  rw [← hyperplaneProduct_nonzeroLocus]
  exact compactifiedSection_mapsTo_nonzero _ _

/-- Relative singular homology map on the genuinely punctured projective product. -/
def canonicalProductRelativeHomologyMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)))
    (subspaceInclusion (compactifiedNonzeroBundle (V := (hyperplaneProductStage K).Model)
      (E := (hyperplaneProductStage K).Fiber)))
    (subspaceMap _ _ (compactifiedSection _ (continuous_hyperplaneProductSection K))
      (canonicalProduct_mapsTo_nonzero K))
    (TopCat.ofHom (compactifiedSection _ (continuous_hyperplaneProductSection K)))
    (subspaceMap_square _ _ _ _) n

theorem canonicalProductRelativeHomology_comparison (n : ℕ) :
    absoluteToRelative
        (subspaceInclusion ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) n ≫
        canonicalProductRelativeHomologyMap K n =
      canonicalProductHomologyMap K n ≫
        absoluteToRelative (subspaceInclusion
          (compactifiedNonzeroBundle (V := (hyperplaneProductStage K).Model)
            (E := (hyperplaneProductStage K).Fiber))) n :=
  absoluteToRelative_naturality _ _ _ _ _ n

/-- Exact missing class obligation for the existing global map. This theorem
is conditional and is not a proof of canonical nonvanishing. -/
theorem canonicalProductHomology_ne_zero_of_relativeClass (n : ℕ)
    (c : relativeSingularHomology
      (subspaceInclusion ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (n+1))
    (hc : relativeHomologyBoundary
      (subspaceInclusion ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) n c = 0)
    (hne : canonicalProductRelativeHomologyMap K (n+1) c ≠ 0) :
    canonicalProductHomologyMap K (n+1) ≠ 0 := by
  obtain ⟨b, hb⟩ := (relativeClass_lifts_iff _ n c).mp hc
  intro hz
  have h := canonicalProductRelativeHomology_comparison K (n+1)
  rw [hz, Limits.zero_comp] at h
  have he := congrArg (fun f => f b) h
  exact hne (by simpa [← hb] using he)

/-- Actual section coordinate map as a continuous map on the full graph model. -/
def canonicalProductCoordinateMap :
    C(ProjectiveProductModel K, ((Σ i, Fin (K i)) → ℂ)) :=
  ⟨canonicalProductSectionCoordinates K, by
    have h : canonicalProductSectionCoordinates K = productSlopeEvaluationEquiv K :=
      funext (canonicalProductSectionCoordinates_eq K)
    rw [h]
    exact (productSlopeEvaluationEquiv K).continuous⟩

theorem canonicalProductCoordinateMap_nonzero :
    Set.MapsTo (canonicalProductCoordinateMap K)
      ({0}ᶜ : Set (ProjectiveProductModel K))
      ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)) := by
  intro A hA
  change A ≠ 0 at hA
  change canonicalProductSectionCoordinates K A ≠ 0
  rw [show canonicalProductSectionCoordinates K A = productSlopeEvaluationEquiv K A from
    canonicalProductSectionCoordinates_eq K A]
  exact fun h => hA ((productSlopeEvaluationEquiv K).injective (h.trans (map_zero _).symm))

def canonicalProductCoordinateRelativeMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({0}ᶜ : Set (ProjectiveProductModel K)))
    (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)))
    (subspaceMap _ _ (canonicalProductCoordinateMap K) (canonicalProductCoordinateMap_nonzero K))
    (TopCat.ofHom (canonicalProductCoordinateMap K)) (subspaceMap_square _ _ _ _) n

/-- The local coordinate map induces an isomorphism on genuine relative
singular homology. This does not assert that these homology groups are nonzero. -/
def canonicalProductCoordinateRelativeIso (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set (ProjectiveProductModel K))) n ≅
      relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ))) n :=
  relativeHomologyHomeomorphIso (productSlopeEvaluationEquiv K).toHomeomorph _ _
    (fun A => by
      change (A ≠ 0) ↔ (productSlopeEvaluationEquiv K A ≠ 0)
      have h : productSlopeEvaluationEquiv K A = 0 ↔ A = 0 := by
        constructor
        · intro hz
          exact (productSlopeEvaluationEquiv K).injective (hz.trans (map_zero _).symm)
        · rintro rfl
          exact map_zero _
      exact (not_congr h).symm) n

theorem canonicalProductCoordinateRelativeIso_hom (n : ℕ) :
    (canonicalProductCoordinateRelativeIso K n).hom = canonicalProductCoordinateRelativeMap K n := by
  have h : canonicalProductCoordinateMap K = ⟨productSlopeEvaluationEquiv K, (productSlopeEvaluationEquiv K).continuous⟩ := by
    apply ContinuousMap.ext
    intro A
    exact canonicalProductSectionCoordinates_eq K A
  unfold canonicalProductCoordinateRelativeIso canonicalProductCoordinateRelativeMap
  rw [relativeHomologyHomeomorphIso_hom]
  simp only [h]
  rfl

theorem canonicalProductCoordinateRelativeMap_isIso (n : ℕ) :
    IsIso (canonicalProductCoordinateRelativeMap K n) := by
  rw [← canonicalProductCoordinateRelativeIso_hom]
  infer_instance

end

open Bundle Topology CategoryTheory
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem canonicalProductGraphChart_target_univ :
    (canonicalProductGraphChart K).target = Set.univ := by
  ext A
  simp [canonicalProductGraphChart]

/-- The actual open neighborhood of the unique zero is homeomorphic to
the full complex graph model, with the inherited topology on the neighborhood. -/
def canonicalProductChartHomeomorph :
    (canonicalProductGraphChart K).source ≃ₜ ProjectiveProductModel K :=
  (canonicalProductGraphChart K).toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (canonicalProductGraphChart_target_univ K)).trans
      (Homeomorph.Set.univ _))

theorem canonicalProductChartHomeomorph_apply
    (P : (canonicalProductGraphChart K).source) :
    canonicalProductChartHomeomorph K P = canonicalProductGraphChart K P := rfl

theorem canonicalProductChartHomeomorph_zero :
    canonicalProductChartHomeomorph K
      ⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩ = 0 :=
  canonicalProductGraphChart_zero K

def canonicalLocalSectionMap :
    C((canonicalProductGraphChart K).source, ((Σ i, Fin (K i)) → ℂ)) :=
  (canonicalProductCoordinateMap K).comp
    ⟨canonicalProductChartHomeomorph K, (canonicalProductChartHomeomorph K).continuous⟩

def canonicalLocalSectionHomeomorph :
    (canonicalProductGraphChart K).source ≃ₜ ((Σ i, Fin (K i)) → ℂ) :=
  (canonicalProductChartHomeomorph K).trans (productSlopeEvaluationEquiv K).toHomeomorph

theorem canonicalLocalSectionMap_eq (P : (canonicalProductGraphChart K).source) :
    canonicalLocalSectionMap K P = canonicalLocalSectionHomeomorph K P :=
  canonicalProductSectionCoordinates_eq K _

theorem canonicalLocalSectionHomeomorph_zero :
    canonicalLocalSectionHomeomorph K
      ⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩ = 0 := by
  change productSlopeEvaluationEquiv K (canonicalProductChartHomeomorph K _) = 0
  rw [canonicalProductChartHomeomorph_zero]
  exact map_zero _

/-- Local section-coordinate isomorphism for the actual punctured chart,
not just an abstract vector-space model. Excision into the full base is separate. -/
def canonicalLocalRelativeHomologyIso (n : ℕ) :
    relativeSingularHomology (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source)) n ≅
      relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ))) n :=
  relativeHomologyHomeomorphIso (canonicalLocalSectionHomeomorph K) _ _ (fun P => by
    change (P ≠ ⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩) ↔
      canonicalLocalSectionHomeomorph K P ≠ 0
    rw [← canonicalLocalSectionHomeomorph_zero K]
    exact (not_congr (canonicalLocalSectionHomeomorph K).injective.eq_iff).symm) n

/-- Inclusion of the punctured chart into the punctured whole base. Its
induced map is constructed; no excision isomorphism is asserted here. -/
def canonicalChartRelativeInclusion (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source))
    (subspaceInclusion ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)))
    (subspaceMap _ _ ⟨Subtype.val, continuous_subtype_val⟩ (by
      intro P hP
      change (P : ProjectiveProduct K) ≠ firstCoordinateProduct K
      intro hz
      exact hP (Subtype.ext hz)))
    (subspaceInclusion (canonicalProductGraphChart K).source)
    (subspaceMap_square _ _ _ _) n

end

end Kaplansky

end

end OAI
