import OAI.AlgebraicTopology.IntegralHomology.GraphNormalization
import OAI.Geometry.BundleTests.Complement

namespace OAI

noncomputable section

namespace Kaplansky

/-! Survival of hyperplane fiber classes and nonvanishing Thom obstructions. -/

section
open Bundle Topology CategoryTheory Limits
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem graphBundleChartNormalization_isIso (F : ∀ i, GraphFrame 1 (K i)) (n : ℕ) :
    IsIso (graphBundleChartNormalization K F n) := by
  have hpiso := productPairProjection_isIso (B := ProjectiveProductModel K)
    ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)) n
  unfold graphBundleChartNormalization graphBundleNormalization
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (graphBundleRelativeIso K _ _ _ _ n).isIso_hom hpiso

/-- Every graph-chart fiber class survives inclusion into the whole
actual bundle pair in fiber degree. The global normalization provides
a left inverse up to the proved local isomorphism. -/
theorem graphBundleChartToAmbient_mono (F : ∀ i, GraphFrame 1 (K i))
    (hp : 0 < ∑ i, K i) :
    Mono (restrictedPairToAmbientHomologyMap (graphBundleChartDomain K F)
      nonzeroBundle (2*(∑ i, K i))) := by
  obtain ⟨f,hf⟩ := hyperplaneBundle_exists_global_normalization K F hp
  have : IsIso (restrictedPairToAmbientHomologyMap (graphBundleChartDomain K F)
      nonzeroBundle (2*(∑ i, K i)) ≫ f) := by
    rw [hf]
    exact graphBundleChartNormalization_isIso K F _
  exact mono_of_mono (restrictedPairToAmbientHomologyMap (graphBundleChartDomain K F)
    nonzeroBundle (2*(∑ i, K i))) f

/-- The original, preserved integral fiber generator has nonzero image
in the whole hyperplane bundle. No choice of a new generator is involved. -/
theorem canonicalFiberGenerator_whole_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalWholeBundleFiberMap K (2*(∑ i, K i)) (canonicalFiberGenerator K hp) ≠ 0 := by
  have : Mono (restrictedPairToAmbientHomologyMap (canonicalBundleChartDomain K)
      nonzeroBundle (2*(∑ i, K i))) :=
    graphBundleChartToAmbient_mono K (fun i => standardLineGraphFrame (K i)) hp
  rw [← canonicalBundleCoverGenerator_whole_image K hp]
  intro hz
  exact canonicalBundleCoverGenerator_ne_zero K hp
    ((ModuleCat.mono_iff_injective
      (restrictedPairToAmbientHomologyMap (canonicalBundleChartDomain K)
        nonzeroBundle (2*(∑ i, K i)))).mp inferInstance (hz.trans (map_zero _).symm))

/-- The exact dependency recorded in Preserve376: the specified
primitive overlap generator survives the ACTUAL punctured-bundle map. -/
theorem canonicalNormalizedOverlapGenerator_punctured_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalOverlapPuncturedMap K (2*(∑ i, K i))
      (canonicalNormalizedOverlapGenerator K hp) ≠ 0 :=
  (not_congr (canonicalFiberGenerator_zero_iff_overlapGenerator K hp)).mp
    (canonicalFiberGenerator_whole_ne_zero K hp)

theorem canonicalProductOrdinaryRelativeGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalProductOrdinaryRelativeMap K (2*(∑ i, K i))
      (canonicalProductLocalGenerator K hp) ≠ 0 := by
  rw [← canonicalFiberGenerator_whole_image K hp]
  exact canonicalFiberGenerator_whole_ne_zero K hp

theorem canonicalProductRelativeGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalProductRelativeHomologyMap K (2*(∑ i, K i))
      (canonicalProductLocalGenerator K hp) ≠ 0 :=
  (not_congr (canonicalProductRelativeMap_zero_iff K _ _)).mpr
    (canonicalProductOrdinaryRelativeGenerator_ne_zero K hp)

/-- The canonical section sends the preserved integral fundamental
class to a nonzero absolute homology class of the actual compactification. -/
theorem canonicalProductHomology_fundamental_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalProductHomologyMap K (2*(∑ i, K i))
      (projectiveProductFundamentalClass K hp) ≠ 0 := by
  intro hz
  have h := ConcreteCategory.congr_hom
    (canonicalProductRelativeHomology_comparison K (2*(∑ i, K i)))
    (projectiveProductFundamentalClass K hp)
  change canonicalProductRelativeHomologyMap K _
      (absoluteToRelative _ _ (projectiveProductFundamentalClass K hp)) =
    absoluteToRelative _ _ (canonicalProductHomologyMap K _ (projectiveProductFundamentalClass K hp)) at h
  rw [projectiveProductFundamentalClass_localizes, hz, map_zero] at h
  exact canonicalProductRelativeGenerator_ne_zero K hp h

theorem canonicalProductHomologyMap_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalProductHomologyMap K (2*(∑ i, K i)) ≠ 0 := by
  intro h
  apply canonicalProductHomology_fundamental_ne_zero K hp
  rw [h]
  rfl

end

section
open Bundle Topology CategoryTheory
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Every continuous section of the actual hyperplane sum induces a
nonzero homology map in degree 2 sum(K), including degenerate sections. -/
theorem hyperplaneProduct_sectionHomology_ne_zero (hp : 0 < ∑ i, K i)
    (s : ∀ y, (hyperplaneProductStage K).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' (hyperplaneProductStage K).Model y (s y))) :
    sectionHomologyMap s hs (2*(∑ i, K i)) ≠ 0 := by
  rw [← canonicalProductHomologyMap_eq_section s hs]
  exact canonicalProductHomologyMap_ne_zero K hp

/-- A genuine section obstruction for H, the rank-sum(K) hyperplane
sum. It makes no assertion about H with additional trivial summands. -/
theorem hyperplaneProduct_every_section_has_zero (hp : 0 < ∑ i, K i)
    (s : ∀ y, (hyperplaneProductStage K).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' (hyperplaneProductStage K).Model y (s y))) :
    ∃ y, s y = 0 := by
  by_contra hn
  push Not at hn
  exact canonicalProductHomologyMap_ne_zero K hp
    (canonicalProductHomologyMap_eq_zero_of_nonvanishing s hs hn (by omega))

theorem hyperplaneProduct_no_positive_frame (hp : 0 < ∑ i, K i)
    (d : ℕ) (hd : 0 < d) :
    IsEmpty (ContinuousOrthonormalStageFrame (hyperplaneProductStage K) d) := by
  refine ⟨fun f => ?_⟩
  exact canonicalProductHomologyMap_ne_zero K hp
    (canonicalProductHomologyMap_eq_zero_of_frame f hd (by omega))

/-- Nonvanishing survives an actual total-space homeomorphism carrying
a section to a section, by the already proved compactification naturality. -/
theorem hyperplaneProduct_transported_sectionHomology_ne_zero
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {E : ProjectiveProduct K → Type}
    [∀ y, NormedAddCommGroup (E y)] [∀ y, NormedSpace ℂ (E y)]
    [TopologicalSpace (TotalSpace W E)] [FiberBundle W E] [VectorBundle ℂ W E]
    (hp : 0 < ∑ i, K i)
    (e : TotalSpace (hyperplaneProductStage K).Model (hyperplaneProductStage K).Fiber ≃ₜ TotalSpace W E)
    (t : ∀ y, E y) (ht : Continuous (fun y => TotalSpace.mk' W y (t y)))
    (he : ∀ y, e (TotalSpace.mk' (hyperplaneProductStage K).Model y (hyperplaneProductSection K y)) =
      TotalSpace.mk' W y (t y)) :
    sectionHomologyMap t ht (2*(∑ i, K i)) ≠ 0 :=
  (not_congr (sectionHomologyMap_naturality_zero_iff e (hyperplaneProductSection K) t
    (continuous_hyperplaneProductSection K) ht he (2*(∑ i, K i)))).mp
    (canonicalProductHomologyMap_ne_zero K hp)

end

open Bundle Topology CategoryTheory Limits
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Nonvanishing in the genuine disk/sphere Thom quotient, with no
assumed Thom class or characteristic-class identification. -/
theorem hyperplaneThomZeroHomologyMap_ne_zero (hp : 0 < ∑ i, K i) :
    thomZeroHomologyMap (hyperplaneProductStage K) (2*(∑ i, K i)) ≠ 0 := by
  have hcard : 0 < Fintype.card (hyperplaneProductStage K).Slot := by
    change 0 < Fintype.card (Σ i, Fin (K i))
    simpa using hp
  have : Nonempty (hyperplaneProductStage K).Slot := Fintype.card_pos_iff.mp hcard
  intro hz
  have h := hyperplaneThomHomology_comparison (K := K) (2*(∑ i, K i))
  rw [hz, zero_comp] at h
  exact canonicalProductHomologyMap_ne_zero K hp h.symm

theorem retainedTest_hyperplaneDegree_pos {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    0 < ∑ i : Fin R, testProjectiveDimension m R i := by
  have : Nonempty (Fin R) := ⟨⟨0,hR⟩⟩
  exact Finset.sum_pos (fun i _ => testProjectiveDimension_pos hm i) Finset.univ_nonempty

theorem retainedTest_hyperplaneThom_ne_zero {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    thomZeroHomologyMap (hyperplaneProductStage (testProjectiveDimension m R))
      (2*(∑ i : Fin R, testProjectiveDimension m R i)) ≠ 0 :=
  hyperplaneThomZeroHomologyMap_ne_zero _ (retainedTest_hyperplaneDegree_pos hm hR)

theorem retainedTest_hyperplane_every_section_has_zero {m R : ℕ}
    (hm : 0 < m) (hR : 0 < R)
    (s : ∀ y, (hyperplaneProductStage (testProjectiveDimension m R)).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk'
      (hyperplaneProductStage (testProjectiveDimension m R)).Model y (s y))) :
    ∃ y, s y = 0 :=
  hyperplaneProduct_every_section_has_zero _ (retainedTest_hyperplaneDegree_pos hm hR) s hs

end

end Kaplansky

end

end OAI
