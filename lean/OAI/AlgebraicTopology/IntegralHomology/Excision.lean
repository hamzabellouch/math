import OAI.AlgebraicTopology.IntegralHomology.HyperplaneLocal
import OAI.AlgebraicTopology.IntegralHomology.SmallExcision
import OAI.AlgebraicTopology.IntegralHomology.Smallness
import Mathlib.Topology.Algebra.Group.Basic

namespace OAI

noncomputable section

namespace Kaplansky

/-! Excision for chart-small chains, open covers, and open embeddings. -/

section
open CategoryTheory Limits
variable {X : Type} [TopologicalSpace X] (U : Set X) (x : X) (hx : x ∈ U)

/-- The punctured subspace and its ambient intersection have the same
inherited topology, with the same underlying points. -/
def puncturedChartIntersectionHomeomorph (U : Set X) (x : X) (hx : x ∈ U) :
    ({⟨x, hx⟩}ᶜ : Set U) ≃ₜ ↥(U ∩ ({x}ᶜ : Set X)) := by
  let f : ({⟨x, hx⟩}ᶜ : Set U) → ↥(U ∩ ({x}ᶜ : Set X)) := fun p =>
    ⟨p.val.val, p.val.property, fun he => p.property (Subtype.ext he)⟩
  let g : ↥(U ∩ ({x}ᶜ : Set X)) → ({⟨x, hx⟩}ᶜ : Set U) := fun p =>
    ⟨⟨p.val, p.property.1⟩, fun he => p.property.2 (congrArg Subtype.val he)⟩
  refine
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · exact (continuous_subtype_val.subtype_mk _).subtype_mk _

def puncturedChartRelativeChainsIso :
    relativeSingularChains (subspaceInclusion ({⟨x, hx⟩}ᶜ : Set U)) ≅
      relativeSingularChains (subspaceInclusionOfLE
        (Set.inter_subset_left : U ∩ ({x}ᶜ : Set X) ⊆ U)) :=
  cokernel.mapIso _ _
    (integralSingularChains.mapIso (TopCat.isoOfHomeo
      (puncturedChartIntersectionHomeomorph U x hx))) (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
      rw [← Functor.map_comp]
      rfl)

def chartRelativeChainInclusion :
    relativeSingularChains (subspaceInclusion ({⟨x, hx⟩}ᶜ : Set U)) ⟶
      relativeSingularChains (subspaceInclusion ({x}ᶜ : Set X)) :=
  relativeChainMap _ _
    (subspaceMap _ _ ⟨Subtype.val, continuous_subtype_val⟩ (by
      intro p hp he
      exact hp (Subtype.ext he)))
    (subspaceInclusion U) (subspaceMap_square _ _ _ _)

/-- Local relative chains are isomorphic to the small relative chains
of the actual cover by the chart and the punctured ambient space. -/
def chartSmallRelativeChainsIso :
    relativeSingularChains (subspaceInclusion ({⟨x, hx⟩}ᶜ : Set U)) ≅
      smallRelativeChains U ({x}ᶜ : Set X) :=
  puncturedChartRelativeChainsIso U x hx ≪≫ smallRelativeExcisionIso U ({x}ᶜ : Set X)

theorem chartSmallRelativeChainsIso_comparison :
    (chartSmallRelativeChainsIso U x hx).hom ≫
        smallRelativeComparison U ({x}ᶜ : Set X) = chartRelativeChainInclusion U x hx := by
  simp only [chartSmallRelativeChainsIso, Iso.trans_hom, Category.assoc,
    smallRelativeExcision_comparison]
  apply (cancel_epi (relativeChainProjection (subspaceInclusion
    ({⟨x, hx⟩}ᶜ : Set U)))).mp
  simp only [puncturedChartRelativeChainsIso, relativeChainProjection,
    chartRelativeChainInclusion, relativeChainMap, cokernel.mapIso_hom, Iso.refl_hom]
  erw [cokernel.π_desc_assoc, Category.id_comp, cokernel.π_desc, cokernel.π_desc]

omit [TopologicalSpace X] in
theorem chart_punctured_cover (U : Set X) (x : X) (hx : x ∈ U) :
    U ∪ ({x}ᶜ : Set X) = Set.univ := by
  ext y
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  by_cases h : y = x
  · exact Or.inl (h ▸ hx)
  · exact Or.inr h

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

def canonicalChartSmallRelativeIso (n : ℕ) :
    relativeSingularHomology (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source)) n ≅
      (smallRelativeChains (canonicalProductGraphChart K).source
        ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (chartSmallRelativeChainsIso _ _ (canonicalProduct_zero_in_chart K))

/-- Exact factorization of the preserved projective-chart inclusion.
The first factor is proved invertible. The second still needs subdivision. -/
theorem canonicalChartRelativeInclusion_factor (n : ℕ) :
    canonicalChartRelativeInclusion K n =
    (canonicalChartSmallRelativeIso K n).hom ≫
        HomologicalComplex.homologyMap
          (smallRelativeComparison (canonicalProductGraphChart K).source
            ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) n := by
  change HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp]
  rw [chartSmallRelativeChainsIso_comparison]
  rfl

theorem canonicalChartRelativeInclusion_isIso_of_smallChains
    (h : QuasiIso (smallSingularChainInclusion (canonicalProductGraphChart K).source
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)))) (n : ℕ) :
    IsIso (canonicalChartRelativeInclusion K n) := by
  have hq := smallRelativeComparison_quasiIso _ _ h
  have hi := (quasiIsoAt_iff_isIso_homologyMap _ n).mp ((quasiIso_iff _).mp hq n)
  rw [canonicalChartRelativeInclusion_factor]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (canonicalChartSmallRelativeIso K n).isIso_hom hi

theorem canonicalChart_punctured_open_cover :
    IsOpen (canonicalProductGraphChart K).source ∧
    IsOpen ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)) ∧
    (canonicalProductGraphChart K).source ∪
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)) = Set.univ :=
  ⟨(canonicalProductGraphChart K).open_source, isClosed_singleton.isOpen_compl,
    chart_punctured_cover _ _ (canonicalProduct_zero_in_chart K)⟩

end

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Comparison from the homology of small chains to full integral singular
homology for a genuine two-set open cover. -/
def openCoverSmallHomologyIso (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (smallSingularChains U V).homology n ≅ (integralSingularChains.obj (TopCat.of X)).homology n := by
  haveI := smallSingularChainInclusion_quasiIso U V hU hV hUV
  exact isoOfQuasiIsoAt (smallSingularChainInclusion U V) n

/-- Singular relative excision for an actual two-set open cover. -/
theorem openCover_relativeInclusion_isIso (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (relativeHomologyMap
      (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U))
      (subspaceInclusion V)
      (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V))
      (subspaceInclusion U) (by rfl) n) :=
  relativeInclusion_isIso_of_smallChains U V
    (smallSingularChainInclusion_quasiIso U V hU hV hUV) n

/-- Full singular Mayer–Vietoris boundary isomorphism for a cover by two
contractible open subspaces, in degrees at least two. -/
def openCoverMayerVietorisBoundaryIso [ContractibleSpace U] [ContractibleSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) (hn : n ≠ 0) :
    (integralSingularHomology (n+1)).obj (TopCat.of X) ≅
      (integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)) :=
  (openCoverSmallHomologyIso U V hU hV hUV (n+1)).symm ≪≫
    smallMayerVietorisBoundaryIso U V n hn

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The preserved canonical projective-chart relative inclusion is now
proved invertible, with no small-chain or excision premise. -/
theorem canonicalChartRelativeInclusion_isIso (n : ℕ) :
    IsIso (canonicalChartRelativeInclusion K n) := by
  obtain ⟨hU, hV, hUV⟩ := canonicalChart_punctured_open_cover K
  exact canonicalChartRelativeInclusion_isIso_of_smallChains K
    (smallSingularChainInclusion_quasiIso _ _ hU hV hUV) n

/-- Actual local singular homology equivalence for the canonical chart. -/
def canonicalChartExcisionIso (n : ℕ) :=
  @asIso _ _ _ _ (canonicalChartRelativeInclusion K n) (canonicalChartRelativeInclusion_isIso K n)

end

section
open CategoryTheory Limits HomologicalComplex Topology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inverse-image pair of an embedding is the actual intersection pair
in its image, including its inherited subspace topology. -/
def embeddingRelativeChainsIso (f : C(X,Y)) (hf : IsEmbedding f) (V : Set Y) :
    relativeSingularChains (subspaceInclusion (f ⁻¹' V)) ≅
      relativeSingularChains (subspaceInclusionOfLE
        (Set.inter_subset_left : Set.range f ∩ V ⊆ Set.range f)) :=
  cokernel.mapIso _ _
    (integralSingularChains.mapIso (TopCat.isoOfHomeo
      ((Homeomorph.setCongr (show f ⁻¹' V = f ⁻¹' (Set.range f ∩ V) by
        ext x
        exact ⟨fun hx => ⟨⟨x,rfl⟩,hx⟩,fun hx => hx.2⟩)).trans
        (hf.homeomorphOfSubsetRange (Set.inter_subset_left : Set.range f ∩ V ⊆ Set.range f)))))
    (integralSingularChains.mapIso (TopCat.isoOfHomeo hf.toHomeomorph)) (by
      simp only [Functor.mapIso_hom]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

/-- Exact chain factorization through the image pair. -/
theorem embeddingRelativeChainsIso_comparison (f : C(X,Y)) (hf : IsEmbedding f)
    (V : Set Y) :
    (embeddingRelativeChainsIso f hf V).hom ≫ relativeChainMap
      (subspaceInclusionOfLE (Set.inter_subset_left : Set.range f ∩ V ⊆ Set.range f))
      (subspaceInclusion V)
      (subspaceInclusionOfLE (Set.inter_subset_right : Set.range f ∩ V ⊆ V))
      (subspaceInclusion (Set.range f)) (by rfl) =
    relativeChainMap (subspaceInclusion (f ⁻¹' V)) (subspaceInclusion V)
      (subspaceMap _ _ f (fun _ h => h)) (TopCat.ofHom f) (by rfl) := by
  apply (cancel_epi (relativeChainProjection (subspaceInclusion (f ⁻¹' V)))).mp
  simp only [embeddingRelativeChainsIso, relativeChainProjection, relativeChainMap,
    cokernel.mapIso_hom, Functor.mapIso_hom]
  erw [cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
  erw [← Category.assoc, ← Functor.map_comp]
  rfl

/-- Excision for an actual open embedding, when its image and the removed
open subspace cover the target. The map is the original map of pairs. -/
theorem openEmbedding_relativeHomologyMap_isIso (f : C(X,Y)) (hf : IsOpenEmbedding f)
    (V : Set Y) (hV : IsOpen V) (hcover : Set.range f ∪ V = Set.univ) (n : ℕ) :
    IsIso (relativeHomologyMap (subspaceInclusion (f ⁻¹' V)) (subspaceInclusion V)
      (subspaceMap _ _ f (fun _ h => h)) (TopCat.ofHom f) (by rfl) n) := by
  have hi := openCover_relativeInclusion_isIso (Set.range f) V hf.isOpen_range hV hcover n
  unfold relativeHomologyMap
  rw [← embeddingRelativeChainsIso_comparison f hf.isEmbedding V, homologyMap_comp]
  change IsIso ((homologyFunctor _ _ n).map (embeddingRelativeChainsIso f hf.isEmbedding V).hom ≫
    relativeHomologyMap _ _ _ _ _ n)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    ((homologyFunctor _ _ n).mapIso (embeddingRelativeChainsIso f hf.isEmbedding V)).isIso_hom hi

end

open CategoryTheory Limits HomologicalComplex
section
variable {X : Type} [TopologicalSpace X] [T1Space X]

/-- Excision at any point of an open chart, using the preserved chain-level
comparison and the proved open-cover small-chain theorem. -/
def openChartLocalExcisionIso (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({⟨x,hx⟩}ᶜ : Set U)) n ≅
      relativeSingularHomology (subspaceInclusion ({x}ᶜ : Set X)) n := by
  haveI := smallRelativeComparison_quasiIso U ({x}ᶜ : Set X)
    (smallSingularChainInclusion_quasiIso U _ hU isClosed_singleton.isOpen_compl
      (chart_punctured_cover U x hx))
  exact (homologyFunctor _ _ n).mapIso (chartSmallRelativeChainsIso U x hx) ≪≫
    isoOfQuasiIsoAt (smallRelativeComparison U ({x}ᶜ : Set X)) n

/-- The excision isomorphism is precisely the actual inclusion of local chains. -/
theorem openChartLocalExcisionIso_hom (U : Set X) (hU : IsOpen U)
    (x : X) (hx : x ∈ U) (n : ℕ) :
    (openChartLocalExcisionIso U hU x hx n).hom =
      homologyMap (chartRelativeChainInclusion U x hx) n := by
  change homologyMap _ n ≫ homologyMap _ n = _
  rw [← homologyMap_comp, chartSmallRelativeChainsIso_comparison]

/-- Center an arbitrary full vector-space chart at the point under study. -/
def centeredChartHomeomorph {E : Type} [NormedAddCommGroup E]
    (U : Set X) (x : X) (hx : x ∈ U) (e : U ≃ₜ E) : U ≃ₜ E :=
  e.trans (Homeomorph.addRight (-e ⟨x,hx⟩))

omit [T1Space X] in
theorem centeredChartHomeomorph_center {E : Type} [NormedAddCommGroup E]
    (U : Set X) (x : X) (hx : x ∈ U) (e : U ≃ₜ E) :
    centeredChartHomeomorph U x hx e ⟨x,hx⟩ = 0 := by
  simp [centeredChartHomeomorph]

/-- Local homology in a full open vector-space chart, at an arbitrary point. -/
def openChartCoordinateLocalHomologyIso {E : Type} [NormedAddCommGroup E]
    (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U) (e : U ≃ₜ E) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({x}ᶜ : Set X)) n ≅
      relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set E)) n :=
  (openChartLocalExcisionIso U hU x hx n).symm ≪≫
    relativeHomologyHomeomorphIso (centeredChartHomeomorph U x hx e) _ _
      (fun y => by
        change y ≠ ⟨x,hx⟩ ↔ centeredChartHomeomorph U x hx e y ≠ 0
        rw [← centeredChartHomeomorph_center U x hx e]
        exact (not_congr (centeredChartHomeomorph U x hx e).injective.eq_iff).symm) n

end

end Kaplansky

end

end OAI
