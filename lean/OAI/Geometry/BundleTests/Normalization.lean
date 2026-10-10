import OAI.AlgebraicTopology.IntegralHomology.FrameNormalization
import OAI.Geometry.BundleTests.Twisted

namespace OAI

noncomputable section

/-! Twisted bundle graph normalization and its naturality. -/

section
open Bundle Topology CategoryTheory Limits Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ) (h : ℕ)
  (U : Set (ProjectiveProduct (twistedProjectiveDimensions K h))) (e : U ≃ₜ A)

theorem twistedCoordinateSpace_real_finrank :
    Module.finrank ℝ (TwistedHyperplaneSlot K h → ℂ) = 2*(h+∑ i, K i) := by
  rw [finrank_real_of_complex]
  simp [TwistedHyperplaneSlot, Fintype.card_sigma, Nat.mul_comm]

def twistedGraphBundlePullbackRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso
    (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm
    (Subtype.val ⁻¹' nonzeroBundle)
    {z : TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
      (finiteLineSumCore (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s)
        (chartBaseMap U e))).Fiber | z.2 ≠ 0}
    (fun z => mem_nonzeroBundle z.1) n

theorem twistedGraphBundleNormalization_pullback
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (hF : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source) (n : ℕ) :
    twistedGraphBundleNormalization K h U e F hF n =
      (twistedGraphBundlePullbackRelativeIso K h U e n).hom ≫
        finiteLineFrameNormalization
          (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
          (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
          (continuous_twistedGraphLineUnit K h U e F hF) n := by
  have he := relativeHomologyHomeomorphIso_trans_hom
    (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm
    (finiteLineFrameHomeomorph
      (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
      (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
      (continuous_twistedGraphLineUnit K h U e F hF))
    (Subtype.val ⁻¹' nonzeroBundle) {z | z.2 ≠ 0} {z | z.2 ≠ 0}
    (fun z => mem_nonzeroBundle z.1)
    (fun z => (not_congr (finiteLineFrameHomeomorph_zero_iff _ _ _ _ z)).symm) n
  exact (congrArg (fun g => g ≫
    productPairProjection (B := A) ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n)
    he).trans (Category.assoc _ _ _)

variable {E V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Fintype J]

theorem twistedGraphBundleNormalization_affine_eq
    (l : J → E →L[ℝ] V) (c : J → V) (a : U ≃ₜ affineAvoidanceSet l c)
    (F₁ F₂ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (h₁ : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F₁).source)
    (h₂ : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F₂).source)
    (hp : 0 < h+∑ i, K i) :
    twistedGraphBundleNormalization K h U a F₁ h₁ (2*(h+∑ i, K i)) =
      twistedGraphBundleNormalization K h U a F₂ h₂ (2*(h+∑ i, K i)) := by
  rw [twistedGraphBundleNormalization_pullback,twistedGraphBundleNormalization_pullback]
  apply congrArg (fun f => (twistedGraphBundlePullbackRelativeIso K h U a (2*(h+∑ i, K i))).hom ≫ f)
  have hv : 2 ≤ Module.finrank ℝ (TwistedHyperplaneSlot K h → ℂ) := by
    rw [twistedCoordinateSpace_real_finrank]; omega
  have he := affineAvoidance_finiteLineFrameNormalization_eq (S := TwistedHyperplaneSlot K h) l c
    (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U a))
    (twistedGraphLineUnit K h U a F₁ h₁) (twistedGraphLineUnit_ne_zero K h U a F₁ h₁)
    (continuous_twistedGraphLineUnit K h U a F₁ h₁)
    (twistedGraphLineUnit K h U a F₂ h₂) (twistedGraphLineUnit_ne_zero K h U a F₂ h₂)
    (continuous_twistedGraphLineUnit K h U a F₂ h₂) hv
  rwa [twistedCoordinateSpace_real_finrank] at he

variable {L : Type} [Fintype L]

theorem twistedGraphBundleIntersection_below_isZero
    (F₀ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (G : L → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (hp : 0 < h+∑ i, K i) (q : ℕ) (hq : q < 2*(h+∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set (twistedGraphBundleDomain K h
        (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F₀ G)))) q) := by
  apply (affineAvoidance_product_below_isZero
    (productGraphDenominatorLinear (twistedProjectiveDimensions K h) F₀ G)
    (productGraphDenominatorConstant (twistedProjectiveDimensions K h) F₀ G)
    (V := TwistedHyperplaneSlot K h → ℂ) ?_ q ?_).of_iso
    (twistedGraphBundleRelativeIso K h
      (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F₀ G)
      (projectiveProductGraphIntersectionHomeomorph (twistedProjectiveDimensions K h) F₀ G)
      F₀ inter_subset_left q)
  · rw [twistedCoordinateSpace_real_finrank]; omega
  · rwa [twistedCoordinateSpace_real_finrank]

end Kaplansky

end

section
open Bundle Topology CategoryTheory Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A B : Type} [Fintype ι] [TopologicalSpace A] [TopologicalSpace B]
  (K : ι → ℕ) (r : ℕ) {U V : Set (ProjectiveProduct (twistedProjectiveDimensions K r))} (h : U ⊆ V)
  (e : U ≃ₜ A) (f : V ≃ₜ B) (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K r i))
  (hF : V ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K r) F).source)

/-- The fiber coordinate depends only on the original base point,
fiber vector and graph frame, and not on the chosen base coordinates. -/
theorem twistedGraphBundleCoordinates_restrict_fiber (z : twistedGraphBundleDomain K r U) :
    (twistedGraphBundleCoordinates K r V f F hF ⟨z.1,h z.2⟩).2 =
      (twistedGraphBundleCoordinates K r U e F (h.trans hF) z).2 := by
  funext s
  change (show EuclideanSpace ℂ (TwistedHyperplaneSlot K r) from z.1.2) s / (show ℂ from twistedGraphLineUnit K r V f F hF s (f ⟨z.1.proj,h z.2⟩)) =
    (show EuclideanSpace ℂ (TwistedHyperplaneSlot K r) from z.1.2) s / (show ℂ from twistedGraphLineUnit K r U e F (h.trans hF) s (e ⟨z.1.proj,z.2⟩))
  congr 1
  cases s with
  | inl j =>
    simp only [twistedGraphLineUnit,tensorLinePair,twistedOldLabel,productGraphLineUnit]
    congr 1
    simp only [productGraphLineEvaluation,pullbackEvaluationEquiv,
      productGraphLineProjection,productGraphLineVector,chartBaseMap,
      ContinuousMap.comp_apply,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply]
    dsimp [hyperplaneEvaluationEquiv,projectionLineFiberEquiv]
    simp only [Homeomorph.symm_apply_apply]
    rfl
  | inr s =>
    simp only [twistedGraphLineUnit,tensorLinePair,twistedOldLabel,productGraphLineUnit]
    congr 1 <;>
      simp only [productGraphLineEvaluation,pullbackEvaluationEquiv,
        productGraphLineProjection,productGraphLineVector,chartBaseMap,
        ContinuousMap.comp_apply,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] <;>
      dsimp [hyperplaneEvaluationEquiv,projectionLineFiberEquiv] <;>
      simp only [Homeomorph.symm_apply_apply] <;> rfl

/-- Restriction of the normalization on a larger chart is exactly the
normalization of the smaller actual bundle pair, in any base coordinates. -/
theorem twistedGraphBundleNormalization_restrict (n : ℕ) :
    restrictedPairHomologyMap (fun _ hz => h hz : twistedGraphBundleDomain K r U ⊆ twistedGraphBundleDomain K r V)
        nonzeroBundle n ≫ twistedGraphBundleNormalization K r V f F hF n =
      twistedGraphBundleNormalization K r U e F (h.trans hF) n := by
  exact productPairNormalization_restrict
    (Subtype.val ⁻¹' nonzeroBundle) (Subtype.val ⁻¹' nonzeroBundle)
    (subspaceInclusionOfLE (fun _ hz => h hz :
      twistedGraphBundleDomain K r U ⊆ twistedGraphBundleDomain K r V)).hom
    (fun _ hz => hz)
    (twistedGraphBundleCoordinates K r U e F (h.trans hF))
    (twistedGraphBundleCoordinates K r V f F hF)
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K r U e F (h.trans hF) z)).symm)
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K r V f F hF z)).symm)
    (twistedGraphBundleCoordinates_restrict_fiber K r h e f F hF) n

end Kaplansky

end

open Bundle Topology CategoryTheory Limits Set
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

abbrev twistedGraphBundleChartDomain (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) :=
  twistedGraphBundleDomain K h (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source

def twistedGraphBundleChartNormalization (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (n : ℕ) :=
  twistedGraphBundleNormalization K h (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source
    (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl n

/-- The local integral fiber normalizations agree after the actual
inclusions from a pairwise intersection of total-space charts. -/
theorem twistedGraphBundleChartNormalization_compatible
    (F G : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    restrictedPairHomologyMap (inter_subset_left :
      twistedGraphBundleChartDomain K h F ∩ twistedGraphBundleChartDomain K h G ⊆ twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ twistedGraphBundleChartNormalization K h F (2*(h+∑ i, K i)) =
    restrictedPairHomologyMap (inter_subset_right :
      twistedGraphBundleChartDomain K h F ∩ twistedGraphBundleChartDomain K h G ⊆ twistedGraphBundleChartDomain K h G)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ twistedGraphBundleChartNormalization K h G (2*(h+∑ i, K i)) := by
  let U := (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source ∩ (projectiveProductGraphChart (twistedProjectiveDimensions K h) G).source
  let H : Unit → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i) := fun _ => G
  have he : U = projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F H := by
    ext P; simp [U, H, projectiveProductGraphIntersection]
  let e := (Homeomorph.setCongr he).trans (projectiveProductGraphIntersectionHomeomorph (twistedProjectiveDimensions K h) F H)
  change restrictedPairHomologyMap (fun z hz => hz.1 :
      twistedGraphBundleDomain K h U ⊆ twistedGraphBundleChartDomain K h F) nonzeroBundle _ ≫
        twistedGraphBundleNormalization K h _ (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl _ =
    restrictedPairHomologyMap (fun z hz => hz.2 :
      twistedGraphBundleDomain K h U ⊆ twistedGraphBundleChartDomain K h G) nonzeroBundle _ ≫
        twistedGraphBundleNormalization K h _ (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) G) G subset_rfl _
  rw [twistedGraphBundleNormalization_restrict K h inter_subset_left e
      (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl,
    twistedGraphBundleNormalization_restrict K h inter_subset_right e
      (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) G) G subset_rfl]
  exact twistedGraphBundleNormalization_affine_eq K h U (productGraphDenominatorLinear (twistedProjectiveDimensions K h) F H)
    (productGraphDenominatorConstant (twistedProjectiveDimensions K h) F H) e F G inter_subset_left inter_subset_right hp

/-- All finite nonempty intersections of the total-space graph charts
have the required lower relative vanishing. -/
theorem twistedGraphBundleChartIntersection_below_isZero
    (T : Finset (∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))) (ht : T.Nonempty)
    (hp : 0 < h+∑ i, K i) (q : ℕ) (hq : q < 2*(h+∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set ↥(⋂ F ∈ T, twistedGraphBundleChartDomain K h F))) q) := by
  classical
  obtain ⟨F,hF⟩ := ht
  let G : T → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i) := fun t => t.val
  have he : (⋂ H ∈ T, twistedGraphBundleChartDomain K h H) =
      twistedGraphBundleDomain K h (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F G) := by
    ext z
    simp only [mem_iInter]
    change (∀ H, H ∈ T → z.proj ∈ (projectiveProductGraphChart (twistedProjectiveDimensions K h) H).source) ↔
      z.proj ∈ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source ∧
        z.proj ∈ ⋂ t : T, (projectiveProductGraphChart (twistedProjectiveDimensions K h) (G t)).source
    rw [mem_iInter]
    exact ⟨fun h => ⟨h F hF,fun t => h t.val t.property⟩,
      fun h H hH => h.2 ⟨H,hH⟩⟩
  rw [he]
  exact twistedGraphBundleIntersection_below_isZero K h F G hp q hq

/-- A genuine normalization on the WHOLE actual twisted bundle pair,
agreeing with the normalization on any preselected graph chart. -/
theorem twistedHyperplaneBundle_exists_global_normalization
    (F₀ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (nonzeroBundle : Set (TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
          (twistedHyperplaneSumCore K h).Fiber))) (2*(h+∑ i, K i)) ⟶
        relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)))
          (2*(h+∑ i, K i)),
      restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F₀) nonzeroBundle
          (2*(h+∑ i, K i)) ≫ f = twistedGraphBundleChartNormalization K h F₀ (2*(h+∑ i, K i)) := by
  classical
  obtain ⟨S,hF₀,hS⟩ := projectiveProduct_finiteGraphCover (twistedProjectiveDimensions K h) F₀
  have hopen : ∀ F ∈ S, IsOpen (twistedGraphBundleChartDomain K h F) :=
    fun F _ => (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).open_source.preimage (FiberBundle.continuous_proj _ _)
  have hcover : (⋃ F ∈ S, twistedGraphBundleChartDomain K h F) = univ := by
    ext z
    have hz : z.proj ∈ ⋃ F ∈ S, (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source := by
      rw [hS]; trivial
    simpa only [mem_iUnion, twistedGraphBundleChartDomain, twistedGraphBundleDomain,
      mem_ofPred_eq, mem_univ, iff_true] using hz
  let n := 2*(h+∑ i, K i)-1
  have hn : n+1 = 2*(h+∑ i, K i) := by dsimp [n]; omega
  have hex := finiteRelativeOpenCover_exists_glue S (twistedGraphBundleChartDomain K h)
    nonzeroBundle hopen hcover n
    (fun T ht _ q hq => twistedGraphBundleChartIntersection_below_isZero K h T ht hp q (by omega))
    (fun F => twistedGraphBundleChartNormalization K h F (n+1))
    (fun F _ G _ => by rw [hn]; exact twistedGraphBundleChartNormalization_compatible K h F G hp)
  rw [hn] at hex
  obtain ⟨f,hf⟩ := hex
  exact ⟨f,hf F₀ hF₀⟩

end Kaplansky

end

end OAI
