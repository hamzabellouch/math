import OAI.AlgebraicTopology.IntegralHomology.GraphCover
import OAI.AlgebraicTopology.IntegralHomology.LineNormalization

namespace OAI

noncomputable section

namespace Kaplansky

/-! Bundle graph coordinates and natural finite-graph normalization. -/

section
open Bundle Topology CategoryTheory Set
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ)
  (U : Set (ProjectiveProduct K)) (e : U ≃ₜ A)

abbrev graphBundleDomain :=
  {z : TotalSpace (hyperplaneProductStage K).Model (hyperplaneProductStage K).Fiber | z.proj ∈ U}

def graphBundleBaseProjection (s : Σ i, Fin (K i)) : C(A,projectionSpace (1+K s.1) 1) :=
  (projectiveProjectionMap (K s.1)).comp
    ((⟨fun P : ProjectiveProduct K => P s.1, continuous_apply s.1⟩ :
      C(ProjectiveProduct K, Grassmann 1 (K s.1))).comp (chartBaseMap U e))

variable (F : ∀ i, GraphFrame 1 (K i))
  (hF : U ⊆ (projectiveProductGraphChart K F).source)

def graphBundleLineVector (s : Σ i, Fin (K i)) (a : A) :=
  graphLineVector (F s.1) (slopeCoordinate (F s.1) ((chartBaseMap U e a) s.1))

theorem graphBundleLineVector_mem (hF : U ⊆ (projectiveProductGraphChart K F).source)
    (s : Σ i, Fin (K i)) (a : A) :
    graphBundleLineVector K U e F s a ∈ projectionLine (graphBundleBaseProjection K U e s a) := by
  have hp : InGraphChart (F s.1) ((chartBaseMap U e a) s.1).val :=
    hF (e.symm a).property s.1 (mem_univ s.1)
  have he : graphBundleBaseProjection K U e s a =
      graphLineProjection (F s.1) (slopeCoordinate (F s.1) ((chartBaseMap U e a) s.1)) := by
    rw [← projectiveProjectionEquiv_symm_slopePoint, slopePoint_coordinate _ _ hp]
    rfl
  rw [he]
  exact graphLineVector_mem _ _

omit [Fintype ι] in
theorem graphBundleLineVector_ne_zero (s : Σ i, Fin (K i)) (a : A) :
    graphBundleLineVector K U e F s a ≠ 0 := graphLineVector_ne_zero _ _

theorem continuous_graphBundleLineVector (hF : U ⊆ (projectiveProductGraphChart K F).source)
    (s : Σ i, Fin (K i)) :
    Continuous (graphBundleLineVector K U e F s) := by
  apply (continuous_graphLineVector (F s.1)).comp
  exact (grassmannChart (F s.1)).continuousOn.comp_continuous
    ((continuous_apply s.1).comp (chartBaseMap U e).continuous)
    (fun a => hF (e.symm a).property s.1 (mem_univ s.1))

/-- Coordinates on the ORIGINAL hyperplane-sum total space restricted
to any subset of an actual graph chart. The fiber is evaluated on an
explicit nonvanishing graph representative. -/
def graphBundleCoordinates : graphBundleDomain K U ≃ₜ A × ((Σ i, Fin (K i)) → ℂ) :=
  (lineSumChartPullbackHomeomorph
    (fun s : Σ i, Fin (K i) => productLineCore K (some s.1)) U e).symm.trans
    (finiteLineEvaluationHomeomorph (graphBundleBaseProjection K U e)
      (graphBundleLineVector K U e F) (graphBundleLineVector_mem K U e F hF)
      (graphBundleLineVector_ne_zero K U e F) (continuous_graphBundleLineVector K U e F hF))

theorem graphBundleCoordinates_base (z : graphBundleDomain K U) :
    (graphBundleCoordinates K U e F hF z).1 = e ⟨z.1.proj,z.2⟩ := rfl

theorem graphBundleCoordinates_zero_iff (z : graphBundleDomain K U) :
    (graphBundleCoordinates K U e F hF z).2 = 0 ↔ z.1.2 = 0 :=
  (finiteLineEvaluationEquiv (graphBundleBaseProjection K U e)
    (graphBundleLineVector K U e F) (graphBundleLineVector_mem K U e F hF)
    (graphBundleLineVector_ne_zero K U e F) _).map_eq_zero_iff

def graphBundleRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (graphBundleCoordinates K U e F hF)
    (Subtype.val ⁻¹' nonzeroBundle) {z : A × ((Σ i, Fin (K i)) → ℂ) | z.2 ≠ 0}
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (graphBundleCoordinates_zero_iff K U e F hF z)).symm) n

/-- Local normalization in integral fiber homology of the actual bundle
pair. Choice of graph frame and gluing are proved separately. -/
def graphBundleNormalization (n : ℕ) :=
  (graphBundleRelativeIso K U e F hF n).hom ≫
    productPairProjection (B := A) ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)) n

end

section
open Bundle Topology CategoryTheory Limits Set
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ)
  (U : Set (ProjectiveProduct K)) (e : U ≃ₜ A)

/-- Pullback coordinates retain the same fiber and removed zero section. -/
def graphBundlePullbackRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso
    (lineSumChartPullbackHomeomorph
      (fun s : Σ i, Fin (K i) => productLineCore K (some s.1)) U e).symm
    (Subtype.val ⁻¹' nonzeroBundle)
    {z : TotalSpace (EuclideanSpace ℂ (Σ i, Fin (K i)))
      (finiteLineSumCore (fun s => evaluationPullbackCore (graphBundleBaseProjection K U e s))).Fiber |
      z.2 ≠ 0}
    (fun z => mem_nonzeroBundle z.1) n

/-- This factorization uses the original restricted total space on its
left and the actual evaluation-pullback bundle on its right. -/
theorem graphBundleNormalization_pullback (F : ∀ i, GraphFrame 1 (K i))
    (hF : U ⊆ (projectiveProductGraphChart K F).source) (n : ℕ) :
    graphBundleNormalization K U e F hF n =
      (graphBundlePullbackRelativeIso K U e n).hom ≫
        finiteLineEvaluationNormalization (graphBundleBaseProjection K U e)
          (graphBundleLineVector K U e F) (graphBundleLineVector_mem K U e F hF)
          (graphBundleLineVector_ne_zero K U e F) (continuous_graphBundleLineVector K U e F hF) n := by
  have he := relativeHomologyHomeomorphIso_trans_hom
    (lineSumChartPullbackHomeomorph
      (fun s : Σ i, Fin (K i) => productLineCore K (some s.1)) U e).symm
    (finiteLineEvaluationHomeomorph (graphBundleBaseProjection K U e)
      (graphBundleLineVector K U e F) (graphBundleLineVector_mem K U e F hF)
      (graphBundleLineVector_ne_zero K U e F) (continuous_graphBundleLineVector K U e F hF))
    (Subtype.val ⁻¹' nonzeroBundle) {z | z.2 ≠ 0} {z | z.2 ≠ 0}
    (fun z => mem_nonzeroBundle z.1)
    (fun z => (not_congr (finiteLineEvaluationHomeomorph_zero_iff _ _ _ _ _ z)).symm) n
  exact (congrArg (fun g => g ≫
    productPairProjection (B := A) ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)) n) he).trans
    (Category.assoc _ _ _)

variable {E F J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Fintype J]

/-- Two graph frames give the SAME normalization of the actual restricted
bundle whenever its base coordinates are a finite affine complement.
All transition and lower-vanishing obligations are discharged. -/
theorem graphBundleNormalization_affine_eq
    (l : J → E →L[ℝ] F) (c : J → F) (a : U ≃ₜ affineAvoidanceSet l c)
    (F₁ F₂ : ∀ i, GraphFrame 1 (K i))
    (h₁ : U ⊆ (projectiveProductGraphChart K F₁).source)
    (h₂ : U ⊆ (projectiveProductGraphChart K F₂).source)
    (hp : 0 < ∑ i, K i) :
    graphBundleNormalization K U a F₁ h₁ (2*(∑ i, K i)) =
      graphBundleNormalization K U a F₂ h₂ (2*(∑ i, K i)) := by
  rw [graphBundleNormalization_pullback, graphBundleNormalization_pullback]
  congr 1
  have hv : 2 ≤ Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) := by
    rw [canonicalCoordinateSpace_real_finrank]; omega
  have h := affineAvoidance_finiteLineEvaluationNormalization_eq l c
    (graphBundleBaseProjection K U a)
    (graphBundleLineVector K U a F₁) (graphBundleLineVector_mem K U a F₁ h₁)
    (graphBundleLineVector_ne_zero K U a F₁) (continuous_graphBundleLineVector K U a F₁ h₁)
    (graphBundleLineVector K U a F₂) (graphBundleLineVector_mem K U a F₂ h₂)
    (graphBundleLineVector_ne_zero K U a F₂) (continuous_graphBundleLineVector K U a F₂ h₂) hv
  rwa [canonicalCoordinateSpace_real_finrank] at h

variable {L : Type} [Fintype L]

/-- The original hyperplane bundle pair over any finite graph-chart
intersection has no homology below its real fiber rank. -/
theorem graphBundleIntersection_below_isZero
    (F₀ : ∀ i, GraphFrame 1 (K i)) (G : L → ∀ i, GraphFrame 1 (K i))
    (hp : 0 < ∑ i, K i) (q : ℕ) (hq : q < 2*(∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle :
        Set (graphBundleDomain K (projectiveProductGraphIntersection K F₀ G)))) q) := by
  apply (affineAvoidance_product_below_isZero
    (productGraphDenominatorLinear K F₀ G) (productGraphDenominatorConstant K F₀ G)
    (V := (Σ i, Fin (K i)) → ℂ) ?_ q ?_).of_iso
    (graphBundleRelativeIso K (projectiveProductGraphIntersection K F₀ G)
      (projectiveProductGraphIntersectionHomeomorph K F₀ G) F₀ inter_subset_left q)
  · rw [canonicalCoordinateSpace_real_finrank]; omega
  · rwa [canonicalCoordinateSpace_real_finrank]

/-- On an actual finite graph-chart intersection the local normalization
is independent of every graph frame containing that intersection. -/
theorem graphBundleIntersection_normalization_eq
    (F₀ : ∀ i, GraphFrame 1 (K i)) (G : L → ∀ i, GraphFrame 1 (K i))
    (F₁ F₂ : ∀ i, GraphFrame 1 (K i))
    (h₁ : projectiveProductGraphIntersection K F₀ G ⊆ (projectiveProductGraphChart K F₁).source)
    (h₂ : projectiveProductGraphIntersection K F₀ G ⊆ (projectiveProductGraphChart K F₂).source)
    (hp : 0 < ∑ i, K i) :
    graphBundleNormalization K (projectiveProductGraphIntersection K F₀ G)
        (projectiveProductGraphIntersectionHomeomorph K F₀ G) F₁ h₁ (2*(∑ i, K i)) =
      graphBundleNormalization K (projectiveProductGraphIntersection K F₀ G)
        (projectiveProductGraphIntersectionHomeomorph K F₀ G) F₂ h₂ (2*(∑ i, K i)) :=
  graphBundleNormalization_affine_eq K _
    (productGraphDenominatorLinear K F₀ G) (productGraphDenominatorConstant K F₀ G)
    (projectiveProductGraphIntersectionHomeomorph K F₀ G) F₁ F₂ h₁ h₂ hp

end

section
open Bundle Topology CategoryTheory Set
open ComplexGrassmann
variable {ι A B : Type} [Fintype ι] [TopologicalSpace A] [TopologicalSpace B]
  (K : ι → ℕ) {U V : Set (ProjectiveProduct K)} (h : U ⊆ V)
  (e : U ≃ₜ A) (f : V ≃ₜ B) (F : ∀ i, GraphFrame 1 (K i))
  (hF : V ⊆ (projectiveProductGraphChart K F).source)

/-- The fiber coordinate depends only on the original base point,
fiber vector and graph frame, and not on the chosen base coordinates. -/
theorem graphBundleCoordinates_restrict_fiber (z : graphBundleDomain K U) :
    (graphBundleCoordinates K V f F hF ⟨z.1,h z.2⟩).2 =
      (graphBundleCoordinates K U e F (h.trans hF) z).2 := by
  change finiteLineEvaluationEquiv (graphBundleBaseProjection K V f)
      (graphBundleLineVector K V f F) (graphBundleLineVector_mem K V f F hF)
      (graphBundleLineVector_ne_zero K V f F) (f ⟨z.1.proj,h z.2⟩) z.1.2 =
    finiteLineEvaluationEquiv (graphBundleBaseProjection K U e)
      (graphBundleLineVector K U e F) (graphBundleLineVector_mem K U e F (h.trans hF))
      (graphBundleLineVector_ne_zero K U e F) (e ⟨z.1.proj,z.2⟩) z.1.2
  funext s
  simp only [finiteLineEvaluationEquiv, pullbackEvaluationEquiv,
    graphBundleBaseProjection, graphBundleLineVector, chartBaseMap,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  dsimp [hyperplaneEvaluationEquiv, projectionLineFiberEquiv]
  simp only [Homeomorph.symm_apply_apply]
  rfl

/-- Restriction of the normalization on a larger chart is exactly the
normalization of the smaller actual bundle pair, in any base coordinates. -/
theorem graphBundleNormalization_restrict (n : ℕ) :
    restrictedPairHomologyMap (fun _ hz => h hz : graphBundleDomain K U ⊆ graphBundleDomain K V)
        nonzeroBundle n ≫ graphBundleNormalization K V f F hF n =
      graphBundleNormalization K U e F (h.trans hF) n := by
  exact productPairNormalization_restrict
    (Subtype.val ⁻¹' nonzeroBundle : Set (graphBundleDomain K U))
    (Subtype.val ⁻¹' nonzeroBundle : Set (graphBundleDomain K V))
    (subspaceInclusionOfLE (fun _ hz => h hz : graphBundleDomain K U ⊆ graphBundleDomain K V)).hom
    (fun _ hz => hz)
    (graphBundleCoordinates K U e F (h.trans hF)) (graphBundleCoordinates K V f F hF)
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (graphBundleCoordinates_zero_iff K U e F (h.trans hF) z)).symm)
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (graphBundleCoordinates_zero_iff K V f F hF z)).symm)
    (graphBundleCoordinates_restrict_fiber K h e f F hF) n

end

open Bundle Topology CategoryTheory Limits Set
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

abbrev graphBundleChartDomain (F : ∀ i, GraphFrame 1 (K i)) :=
  graphBundleDomain K (projectiveProductGraphChart K F).source

def graphBundleChartNormalization (F : ∀ i, GraphFrame 1 (K i)) (n : ℕ) :=
  graphBundleNormalization K (projectiveProductGraphChart K F).source
    (projectiveProductGraphHomeomorph K F) F subset_rfl n

/-- The local integral fiber normalizations agree after the actual
inclusions from a pairwise intersection of total-space charts. -/
theorem graphBundleChartNormalization_compatible
    (F G : ∀ i, GraphFrame 1 (K i)) (hp : 0 < ∑ i, K i) :
    restrictedPairHomologyMap (inter_subset_left :
      graphBundleChartDomain K F ∩ graphBundleChartDomain K G ⊆ graphBundleChartDomain K F)
      nonzeroBundle (2*(∑ i, K i)) ≫ graphBundleChartNormalization K F (2*(∑ i, K i)) =
    restrictedPairHomologyMap (inter_subset_right :
      graphBundleChartDomain K F ∩ graphBundleChartDomain K G ⊆ graphBundleChartDomain K G)
      nonzeroBundle (2*(∑ i, K i)) ≫ graphBundleChartNormalization K G (2*(∑ i, K i)) := by
  let U := (projectiveProductGraphChart K F).source ∩ (projectiveProductGraphChart K G).source
  let H : Unit → ∀ i, GraphFrame 1 (K i) := fun _ => G
  have he : U = projectiveProductGraphIntersection K F H := by
    ext P; simp [U, H, projectiveProductGraphIntersection]
  let e := (Homeomorph.setCongr he).trans (projectiveProductGraphIntersectionHomeomorph K F H)
  change restrictedPairHomologyMap (fun z hz => hz.1 :
      graphBundleDomain K U ⊆ graphBundleChartDomain K F) nonzeroBundle _ ≫
        graphBundleNormalization K _ (projectiveProductGraphHomeomorph K F) F subset_rfl _ =
    restrictedPairHomologyMap (fun z hz => hz.2 :
      graphBundleDomain K U ⊆ graphBundleChartDomain K G) nonzeroBundle _ ≫
        graphBundleNormalization K _ (projectiveProductGraphHomeomorph K G) G subset_rfl _
  rw [graphBundleNormalization_restrict K inter_subset_left e
      (projectiveProductGraphHomeomorph K F) F subset_rfl,
    graphBundleNormalization_restrict K inter_subset_right e
      (projectiveProductGraphHomeomorph K G) G subset_rfl]
  exact graphBundleNormalization_affine_eq K U (productGraphDenominatorLinear K F H)
    (productGraphDenominatorConstant K F H) e F G inter_subset_left inter_subset_right hp

/-- All finite nonempty intersections of the total-space graph charts
have the required lower relative vanishing. -/
theorem graphBundleChartIntersection_below_isZero
    (T : Finset (∀ i, GraphFrame 1 (K i))) (ht : T.Nonempty)
    (hp : 0 < ∑ i, K i) (q : ℕ) (hq : q < 2*(∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set ↥(⋂ F ∈ T, graphBundleChartDomain K F))) q) := by
  classical
  obtain ⟨F,hF⟩ := ht
  let G : T → ∀ i, GraphFrame 1 (K i) := fun t => t.val
  have he : (⋂ H ∈ T, graphBundleChartDomain K H) =
      graphBundleDomain K (projectiveProductGraphIntersection K F G) := by
    ext z
    simp only [mem_iInter]
    change (∀ H, H ∈ T → z.proj ∈ (projectiveProductGraphChart K H).source) ↔
      z.proj ∈ (projectiveProductGraphChart K F).source ∧
        z.proj ∈ ⋂ t : T, (projectiveProductGraphChart K (G t)).source
    rw [mem_iInter]
    exact ⟨fun h => ⟨h F hF,fun t => h t.val t.property⟩,
      fun h H hH => h.2 ⟨H,hH⟩⟩
  rw [he]
  exact graphBundleIntersection_below_isZero K F G hp q hq

/-- A genuine normalization on the WHOLE actual hyperplane bundle pair,
agreeing with the normalization on any preselected graph chart. -/
theorem hyperplaneBundle_exists_global_normalization
    (F₀ : ∀ i, GraphFrame 1 (K i)) (hp : 0 < ∑ i, K i) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (nonzeroBundle : Set (TotalSpace (hyperplaneProductStage K).Model
          (hyperplaneProductStage K).Fiber))) (2*(∑ i, K i)) ⟶
        relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ)))
          (2*(∑ i, K i)),
      restrictedPairToAmbientHomologyMap (graphBundleChartDomain K F₀) nonzeroBundle
          (2*(∑ i, K i)) ≫ f = graphBundleChartNormalization K F₀ (2*(∑ i, K i)) := by
  classical
  obtain ⟨S,hF₀,hS⟩ := projectiveProduct_finiteGraphCover K F₀
  have hopen : ∀ F ∈ S, IsOpen (graphBundleChartDomain K F) :=
    fun F _ => (projectiveProductGraphChart K F).open_source.preimage (FiberBundle.continuous_proj _ _)
  have hcover : (⋃ F ∈ S, graphBundleChartDomain K F) = univ := by
    ext z
    have hz : z.proj ∈ ⋃ F ∈ S, (projectiveProductGraphChart K F).source := by
      rw [hS]; trivial
    simpa only [mem_iUnion, graphBundleChartDomain, graphBundleDomain,
      mem_ofPred_eq, mem_univ, iff_true] using hz
  let n := 2*(∑ i, K i)-1
  have hn : n+1 = 2*(∑ i, K i) := by dsimp [n]; omega
  have hex := finiteRelativeOpenCover_exists_glue S (graphBundleChartDomain K)
    nonzeroBundle hopen hcover n
    (fun T ht _ q hq => graphBundleChartIntersection_below_isZero K T ht hp q (by omega))
    (fun F => graphBundleChartNormalization K F (n+1))
    (fun F _ G _ => by rw [hn]; exact graphBundleChartNormalization_compatible K F G hp)
  rw [hn] at hex
  obtain ⟨f,hf⟩ := hex
  exact ⟨f,hf F₀ hF₀⟩

end

end Kaplansky

end

end OAI
