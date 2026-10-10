import OAI.AlgebraicTopology.IntegralHomology.SmallExcision
import OAI.AlgebraicTopology.IntegralHomology.Smallness
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative Mayer-Vietoris comparison, exactness, and gluing. -/

section
open CategoryTheory Limits HomologicalComplex

private theorem comp_zero_of_iso {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃)
    (hf : e₁.hom ≫ f' = f ≫ e₂.hom) (hg : e₂.hom ≫ g' = g ≫ e₃.hom)
    (h : f ≫ g = 0) : f' ≫ g' = 0 := by
  apply (cancel_epi e₁.hom).mp
  rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc, h, zero_comp, comp_zero]

section
variable {X : Type} [TopologicalSpace X] (U V A : Set X)

/-- The inclusion of the removed subspace, with its induced two-set cover. -/
def removedCoverSequenceMap :
    smallMayerVietorisSequence (Subtype.val ⁻¹' U : Set A) (Subtype.val ⁻¹' V : Set A) ⟶
      smallMayerVietorisSequence U V :=
  smallMayerVietorisContinuousMap _ _ U V
    ⟨Subtype.val, continuous_subtype_val⟩ (fun _ h => h) (fun _ h => h)

theorem removedCoverSequenceMap_mono : Mono (removedCoverSequenceMap U V A).τ₃ :=
  smallSingularChainsContinuousMap_mono _ _ _ _ _ _ _ Subtype.val_injective

/-- The relative gluing sequence formed using the actual singular chains
of A. Its right term compares directly with C(X)/C(A). -/
def relativeCoverChainSequence := quotientShortComplex (removedCoverSequenceMap U V A)

theorem relativeCoverChainSequence_shortExact :
    (relativeCoverChainSequence U V A).ShortExact := by
  have := removedCoverSequenceMap_mono U V A
  exact quotientShortComplex_shortExact _
    (smallMayerVietorisSequence_shortExact _ _) (smallMayerVietorisSequence_shortExact _ _)

def relativeCoverChainComparison : (relativeCoverChainSequence U V A).X₃ ⟶
    relativeSingularChains (subspaceInclusion A) :=
  cokernel.map _ _ (smallSingularChainInclusion _ _) (smallSingularChainInclusion U V)
    (smallSingularChainsContinuousMap_inclusion _ _ _ _ _ _ _)

def relativeCoverQuotientSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (removedCoverSequenceMap U V A).τ₃ (cokernel.π _)
    (cokernel.condition _)

theorem relativeCoverQuotientSequence_shortExact :
    (relativeCoverQuotientSequence U V A).ShortExact := by
  have := removedCoverSequenceMap_mono U V A
  exact {
    exact := ShortComplex.exact_cokernel _
    mono_f := removedCoverSequenceMap_mono U V A
    epi_g := coequalizer.π_epi (f := (removedCoverSequenceMap U V A).τ₃) (g := 0) }

def relativeCoverQuotientSequenceComparison : relativeCoverQuotientSequence U V A ⟶
    relativeChainSequence (subspaceInclusion A) where
  τ₁ := smallSingularChainInclusion _ _
  τ₂ := smallSingularChainInclusion U V
  τ₃ := relativeCoverChainComparison U V A
  comm₁₂ := (smallSingularChainsContinuousMap_inclusion _ _ _ _ _ _ _).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- Subdivision on both X and A proves comparison with full relative
singular chains. No openness of A is needed. -/
theorem relativeCoverChainComparison_quasiIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) : QuasiIso (relativeCoverChainComparison U V A) := by
  have hA : (Subtype.val ⁻¹' U : Set A) ∪ (Subtype.val ⁻¹' V : Set A) = Set.univ := by
    rw [← Set.preimage_union, hcover, Set.preimage_univ]
  exact HomologySequence.quasiIso_τ₃
    (relativeCoverQuotientSequenceComparison U V A)
    (relativeCoverQuotientSequence_shortExact U V A)
    (relativeChainSequence_shortExact (subspaceInclusion A))
    (smallSingularChainInclusion_quasiIso _ _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) hA)
    (smallSingularChainInclusion_quasiIso U V hU hV hcover)

def relativeOpenCoverHomologyIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (relativeCoverChainSequence U V A).X₃.homology n ≅
      relativeSingularHomology (subspaceInclusion A) n := by
  have := relativeCoverChainComparison_quasiIso U V A hU hV hcover
  exact isoOfQuasiIsoAt (relativeCoverChainComparison U V A) n

end

section
local instance (n : ℕ) : PreservesBinaryBiproducts
    (homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _
variable {X : Type} [TopologicalSpace X]

/-- The same intersection subspace, in the opposite order of its subtypes. -/
def intersectionSubtypeSwap (U A : Set X) :
    (Subtype.val ⁻¹' U : Set A) ≃ₜ (Subtype.val ⁻¹' A : Set U) where
  toFun z := ⟨⟨z.1.1,z.2⟩,z.1.2⟩
  invFun z := ⟨⟨z.1.1,z.2⟩,z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def removedRestrictionMap (U A : Set X) :
    TopCat.of (Subtype.val ⁻¹' U : Set A) ⟶ TopCat.of U :=
  subspaceMap _ U ⟨Subtype.val, continuous_subtype_val⟩ (fun _ h => h)

/-- The relative chain group in a chart uses its actual removed subspace. -/
def removedRestrictionChainsIso (U A : Set X) :
    cokernel (integralSingularChains.map (removedRestrictionMap U A)) ≅
      relativeSingularChains (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) :=
  cokernel.mapIso _ _
    (integralSingularChains.mapIso (TopCat.isoOfHomeo (intersectionSubtypeSwap U A)))
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
      rw [← Functor.map_comp]
      rfl)

@[reassoc (attr := simp)]
theorem removedRestrictionChainsIso_projection (U A : Set X) :
    cokernel.π (integralSingularChains.map (removedRestrictionMap U A)) ≫
      (removedRestrictionChainsIso U A).hom =
        relativeChainProjection (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) := by
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

def relativeCoverLeftChainsIso (U V A : Set X) :
    (relativeCoverChainSequence U V A).X₁ ≅
      relativeSingularChains (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) :=
  removedRestrictionChainsIso (U ∩ V) A

def relativeCoverMiddleChainsIso (U V A : Set X) :
    (relativeCoverChainSequence U V A).X₂ ≅
      relativeSingularChains (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) ⊞
        relativeSingularChains (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) :=
  cokernelBiprodIso _ _ ≪≫
    biprod.mapIso (removedRestrictionChainsIso U A) (removedRestrictionChainsIso V A)

def relativeCoverLeftHomologyIso (U V A : Set X) (n : ℕ) :
    (relativeCoverChainSequence U V A).X₁.homology n ≅
      relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n :=
  (homologyFunctor _ _ n).mapIso (relativeCoverLeftChainsIso U V A)

def relativeCoverMiddleHomologyIso (U V A : Set X) (n : ℕ) :
    (relativeCoverChainSequence U V A).X₂.homology n ≅
      relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n ⊞
        relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) n :=
  (homologyFunctor _ _ n).mapIso (relativeCoverMiddleChainsIso U V A) ≪≫
    (homologyFunctor _ _ n).mapBiprod _ _

end

section
variable {X : Type} [TopologicalSpace X]

/-- Inclusion of restricted pairs (U,U∩A) into (V,V∩A). -/
def restrictedPairChainMap {U V : Set X} (h : U ⊆ V) (A : Set X) :=
  relativeChainMap (subspaceInclusion (Subtype.val ⁻¹' A : Set U))
    (subspaceInclusion (Subtype.val ⁻¹' A : Set V))
    (subspaceMap _ _ (subspaceInclusionOfLE h).hom (fun _ hx => hx))
    (subspaceInclusionOfLE h) (by rfl)

/-- Inclusion of the actual chart pair into the whole pair. -/
def restrictedPairToAmbientChainMap (U A : Set X) :=
  relativeChainMap (subspaceInclusion (Subtype.val ⁻¹' A : Set U))
    (subspaceInclusion A)
    (subspaceMap _ _ ⟨Subtype.val,continuous_subtype_val⟩ (fun _ hx => hx))
    (subspaceInclusion U) (by rfl)

def restrictedPairHomologyMap {U V : Set X} (h : U ⊆ V) (A : Set X) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n ⟶
      relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) n :=
  homologyMap (restrictedPairChainMap h A) n

def restrictedPairToAmbientHomologyMap (U A : Set X) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n ⟶
      relativeSingularHomology (subspaceInclusion A) n :=
  homologyMap (restrictedPairToAmbientChainMap U A) n

theorem restrictedPairChainMap_toAmbient {U V : Set X} (h : U ⊆ V) (A : Set X) :
    restrictedPairChainMap h A ≫ restrictedPairToAmbientChainMap V A =
      restrictedPairToAmbientChainMap U A := by
  unfold restrictedPairChainMap restrictedPairToAmbientChainMap
  erw [relativeChainMap_comp]
  rfl

theorem restrictedPairHomologyMap_toAmbient {U V : Set X} (h : U ⊆ V)
    (A : Set X) (n : ℕ) :
    restrictedPairHomologyMap h A n ≫ restrictedPairToAmbientHomologyMap V A n =
      restrictedPairToAmbientHomologyMap U A n := by
  unfold restrictedPairHomologyMap restrictedPairToAmbientHomologyMap
  erw [← homologyMap_comp, restrictedPairChainMap_toAmbient]

private theorem relativeCoverMiddleChainsIso_projection (U V A : Set X) :
    cokernel.π (removedCoverSequenceMap U V A).τ₂ ≫
      (relativeCoverMiddleChainsIso U V A).hom =
    biprod.map (relativeChainProjection (subspaceInclusion (Subtype.val ⁻¹' A : Set U)))
      (relativeChainProjection (subspaceInclusion (Subtype.val ⁻¹' A : Set V))) := by
  change cokernel.π (biprod.map _ _) ≫
    ((cokernelBiprodIso _ _).hom ≫
      (biprod.mapIso (removedRestrictionChainsIso U A) (removedRestrictionChainsIso V A)).hom) = _
  erw [← Category.assoc, cokernelBiprodIso_projection, biprod.mapIso_hom]
  apply biprod.hom_ext
  · erw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.map_fst,
      Category.assoc, removedRestrictionChainsIso_projection, biprod.map_fst]
  · erw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.map_snd,
      Category.assoc, removedRestrictionChainsIso_projection, biprod.map_snd]

/-- Identification of the left gluing map, including its minus sign, with
the two actual inclusions of intersection pairs. -/
theorem relativeCoverLeftChainsIso_map (U V A : Set X) :
    (relativeCoverLeftChainsIso U V A).hom ≫
      biprod.lift (restrictedPairChainMap (Set.inter_subset_left : U ∩ V ⊆ U) A)
        (-restrictedPairChainMap (Set.inter_subset_right : U ∩ V ⊆ V) A) =
    (relativeCoverChainSequence U V A).f ≫ (relativeCoverMiddleChainsIso U V A).hom := by
  apply (cancel_epi (cokernel.π (removedCoverSequenceMap U V A).τ₁)).mp
  have hl := removedRestrictionChainsIso_projection (U ∩ V) A
  change cokernel.π (removedCoverSequenceMap U V A).τ₁ ≫
    (relativeCoverLeftChainsIso U V A).hom = _ at hl
  erw [← Category.assoc, hl]
  erw [cokernel.π_desc_assoc, Category.assoc, relativeCoverMiddleChainsIso_projection]
  change _ = biprod.lift
    (integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)))
    (-integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V))) ≫ _
  apply biprod.hom_ext
  · erw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst,
      ← Category.assoc (biprod.lift _ _) biprod.fst, biprod.lift_fst]
    exact relativeChainProjection_map _ _ _ _ _
  · erw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd,
      ← Category.assoc (biprod.lift _ _) biprod.snd, biprod.lift_snd,
      Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg (relativeChainProjection_map _ _ _ _ _)

/-- Identification of the right gluing map with the sum of the actual
inclusions into (X,A), after the proved small-to-full chain comparison. -/
theorem relativeCoverMiddleChainsIso_map (U V A : Set X) :
    (relativeCoverMiddleChainsIso U V A).hom ≫
      biprod.desc (restrictedPairToAmbientChainMap U A) (restrictedPairToAmbientChainMap V A) =
    (relativeCoverChainSequence U V A).g ≫ relativeCoverChainComparison U V A := by
  apply (cancel_epi (cokernel.π (removedCoverSequenceMap U V A).τ₂)).mp
  erw [← Category.assoc, relativeCoverMiddleChainsIso_projection]
  erw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc]
  change _ = biprod.desc (singularChainsIntoSmallLeft U V) (singularChainsIntoSmallRight U V) ≫
    smallSingularChainInclusion U V ≫ _
  apply biprod.hom_ext'
  · erw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc,
      ← Category.assoc (singularChainsIntoSmallLeft U V), singularChainsIntoSmallLeft_inclusion]
    exact relativeChainProjection_map _ _ _ _ _
  · erw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc,
      ← Category.assoc (singularChainsIntoSmallRight U V), singularChainsIntoSmallRight_inclusion]
    exact relativeChainProjection_map _ _ _ _ _

end

section
local instance (n : ℕ) : PreservesBinaryBiproducts
    (homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _
variable {X : Type} [TopologicalSpace X] (U V A : Set X)

theorem relativeCoverLeftHomologyIso_map (n : ℕ) :
    (relativeCoverLeftHomologyIso U V A n).hom ≫
      biprod.lift (restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A n)
        (-restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A n) =
    homologyMap (relativeCoverChainSequence U V A).f n ≫
      (relativeCoverMiddleHomologyIso U V A n).hom := by
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  change F.map (relativeCoverLeftChainsIso U V A).hom ≫
    biprod.lift (F.map (restrictedPairChainMap _ A)) (-F.map (restrictedPairChainMap _ A)) =
      F.map (relativeCoverChainSequence U V A).f ≫
        (F.map (relativeCoverMiddleChainsIso U V A).hom ≫ (F.mapBiprod _ _).hom)
  rw [← F.map_neg, ← biprod.map_lift_mapBiprod F, ← Category.assoc,
    ← F.map_comp, relativeCoverLeftChainsIso_map, F.map_comp, Category.assoc]

theorem relativeCoverMiddleHomologyIso_map (n : ℕ) :
    (relativeCoverMiddleHomologyIso U V A n).hom ≫
      biprod.desc (restrictedPairToAmbientHomologyMap U A n) (restrictedPairToAmbientHomologyMap V A n) =
    homologyMap (relativeCoverChainSequence U V A).g n ≫
      homologyMap (relativeCoverChainComparison U V A) n := by
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  change (F.map (relativeCoverMiddleChainsIso U V A).hom ≫ (F.mapBiprod _ _).hom) ≫
    biprod.desc (F.map (restrictedPairToAmbientChainMap U A))
      (F.map (restrictedPairToAmbientChainMap V A)) =
    F.map (relativeCoverChainSequence U V A).g ≫ F.map (relativeCoverChainComparison U V A)
  rw [Category.assoc, biprod.mapBiprod_hom_desc, ← F.map_comp,
    relativeCoverMiddleChainsIso_map, F.map_comp]

/-- The exact relative Mayer–Vietoris sequence at the direct sum, with
the standard signed intersection map and actual pair inclusions. -/
def relativeMayerVietorisSumSequence (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) where
  f := biprod.lift (restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A n)
    (-restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A n)
  g := biprod.desc (restrictedPairToAmbientHomologyMap U A n) (restrictedPairToAmbientHomologyMap V A n)
  zero := by simp [restrictedPairHomologyMap_toAmbient]

def relativeMayerVietorisSumSequenceIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    ((relativeCoverChainSequence U V A).map (homologyFunctor _ _ n)) ≅
      relativeMayerVietorisSumSequence U V A n :=
  ShortComplex.isoMk (relativeCoverLeftHomologyIso U V A n)
    (relativeCoverMiddleHomologyIso U V A n)
    (relativeOpenCoverHomologyIso U V A hU hV hcover n)
    (relativeCoverLeftHomologyIso_map U V A n)
    (relativeCoverMiddleHomologyIso_map U V A n)

theorem relativeMayerVietoris_exact_at_sum (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (relativeMayerVietorisSumSequence U V A n).Exact :=
  ShortComplex.exact_of_iso (relativeMayerVietorisSumSequenceIso U V A hU hV hcover n)
    ((relativeCoverChainSequence_shortExact U V A).homology_exact₂ n)

/-- The connecting map on the actual full relative homology groups. -/
def relativeMayerVietorisBoundary (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :=
  (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1)).inv ≫
    (relativeCoverChainSequence_shortExact U V A).δ (n+1) n rfl ≫
      (relativeCoverLeftHomologyIso U V A n).hom

theorem relativeMayerVietoris_sum_boundary (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (relativeMayerVietorisSumSequence U V A (n+1)).g ≫
      relativeMayerVietorisBoundary U V A hU hV hcover n = 0 := by
  exact comp_zero_of_iso
    (relativeCoverMiddleHomologyIso U V A (n+1))
    (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1))
    (relativeCoverLeftHomologyIso U V A n) _ _ _ _
    (relativeCoverMiddleHomologyIso_map U V A (n+1))
    ((relativeOpenCoverHomologyIso U V A hU hV hcover (n+1)).hom_inv_id_assoc _)
    ((relativeCoverChainSequence_shortExact U V A).comp_δ (n+1) n rfl)

theorem relativeMayerVietoris_exact_at_relative (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _ (relativeMayerVietoris_sum_boundary U V A hU hV hcover n)).Exact := by
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (relativeCoverMiddleHomologyIso U V A (n+1))
      (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1))
      (relativeCoverLeftHomologyIso U V A n)
      (relativeCoverMiddleHomologyIso_map U V A (n+1)) ?_)
    ((relativeCoverChainSequence_shortExact U V A).homology_exact₃ (n+1) n rfl)
  exact (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1)).hom_inv_id_assoc _

end

variable {X : Type} [TopologicalSpace X] (U V A : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
include hU hV hcover

/-- The exact reason a class in one chart can die in the whole pair:
it comes from an overlap class whose image in the other chart is zero. -/
theorem relativeOpenCover_left_image_zero_iff (n : ℕ)
    (z : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n) :
    restrictedPairToAmbientHomologyMap U A n z = 0 ↔
      ∃ w : relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n,
        restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A n w = z ∧
        restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A n w = 0 := by
  constructor
  · intro hz
    let HU := relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n
    let HV := relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) n
    let S := relativeMayerVietorisSumSequence U V A n
    have hex := (S.moduleCat_exact_iff).mp
      (relativeMayerVietoris_exact_at_sum U V A hU hV hcover n)
    have hzero : S.g ((biprod.inl : HU ⟶ HU ⊞ HV) z) = 0 := by
      change ((biprod.inl : HU ⟶ HU ⊞ HV) ≫ biprod.desc _ _) z = 0
      erw [biprod.inl_desc]
      exact hz
    obtain ⟨w, hw⟩ := hex _ hzero
    refine ⟨w, ?_, ?_⟩
    · have h := congrArg (fun x => (biprod.fst : HU ⊞ HV ⟶ HU) x) hw
      change (biprod.lift _ _ ≫ (biprod.fst : HU ⊞ HV ⟶ HU)) w = ((biprod.inl : HU ⟶ HU ⊞ HV) ≫ biprod.fst) z at h
      erw [biprod.lift_fst, biprod.inl_fst] at h
      exact h
    · have h := congrArg (fun x => (biprod.snd : HU ⊞ HV ⟶ HV) x) hw
      change (biprod.lift _ _ ≫ (biprod.snd : HU ⊞ HV ⟶ HV)) w = ((biprod.inl : HU ⟶ HU ⊞ HV) ≫ biprod.snd) z at h
      erw [biprod.lift_snd, biprod.inl_snd] at h
      change -(restrictedPairHomologyMap _ A n w) = 0 at h
      exact neg_eq_zero.mp h
  · rintro ⟨w,rfl,hw⟩
    change (restrictedPairHomologyMap _ A n ≫ restrictedPairToAmbientHomologyMap U A n) w = 0
    rw [restrictedPairHomologyMap_toAmbient]
    rw [← restrictedPairHomologyMap_toAmbient (Set.inter_subset_right : U ∩ V ⊆ V)]
    change restrictedPairToAmbientHomologyMap V A n
      (restrictedPairHomologyMap _ A n w) = 0
    rw [hw, map_zero]

theorem relativeOpenCover_left_mono (n : ℕ)
    (hker : ∀ w : relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n,
      restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A n w = 0 →
      restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A n w = 0) :
    Mono (restrictedPairToAmbientHomologyMap U A n) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y hxy
  have hz : restrictedPairToAmbientHomologyMap U A n (x-y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨w,hw,hv⟩ := (relativeOpenCover_left_image_zero_iff U V A hU hV hcover n _).mp hz
  exact sub_eq_zero.mp (hw.symm.trans (hker w hv))

/-- Below the overlap degree, the two actual chart maps jointly generate
the full relative homology group. -/
theorem relativeOpenCover_sum_epi (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n)) :
    Epi (relativeMayerVietorisSumSequence U V A (n+1)).g := by
  have hex := relativeMayerVietoris_exact_at_relative U V A hU hV hcover n
  exact (ShortComplex.exact_iff_epi _ (hi.eq_of_tgt _ _)).mp hex

/-- Compatible local linear normalizations glue to a genuine global
normalization when the preceding overlap group vanishes. -/
def relativeOpenCoverGlue (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (u : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1) ⟶ Z)
    (v : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1) ⟶ Z)
    (hcompat : restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A (n+1) ≫ u =
      restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A (n+1) ≫ v) :
    relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z := by
  have := relativeOpenCover_sum_epi U V A hU hV hcover n hi
  exact (relativeMayerVietoris_exact_at_sum U V A hU hV hcover (n+1)).desc
    (biprod.desc u v) (by
      dsimp only [relativeMayerVietorisSumSequence]
      erw [biprod.lift_desc, Preadditive.neg_comp, hcompat, add_neg_cancel]
      rfl)

theorem relativeOpenCoverGlue_restrictions (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (u : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1) ⟶ Z)
    (v : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1) ⟶ Z)
    (hcompat : restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A (n+1) ≫ u =
      restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A (n+1) ≫ v) :
    restrictedPairToAmbientHomologyMap U A (n+1) ≫
      relativeOpenCoverGlue U V A hU hV hcover n hi u v hcompat = u ∧
    restrictedPairToAmbientHomologyMap V A (n+1) ≫
      relativeOpenCoverGlue U V A hU hV hcover n hi u v hcompat = v := by
  have := relativeOpenCover_sum_epi U V A hU hV hcover n hi
  have he := (relativeMayerVietoris_exact_at_sum U V A hU hV hcover (n+1)).g_desc
    (biprod.desc u v) (show (relativeMayerVietorisSumSequence U V A (n+1)).f ≫
      biprod.desc u v = 0 by
        dsimp only [relativeMayerVietorisSumSequence]
        erw [biprod.lift_desc, Preadditive.neg_comp, hcompat, add_neg_cancel]
        rfl)
  constructor
  · have hl := congrArg (fun f => biprod.inl ≫ f) he
    dsimp only [relativeMayerVietorisSumSequence] at hl
    erw [biprod.inl_desc_assoc, biprod.inl_desc] at hl
    exact hl
  · have hr := congrArg (fun f => biprod.inr ≫ f) he
    dsimp only [relativeMayerVietorisSumSequence] at hr
    erw [biprod.inr_desc_assoc, biprod.inr_desc] at hr
    exact hr

end

open CategoryTheory Limits HomologicalComplex
section
variable {X : Type} [TopologicalSpace X] (U V A : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

theorem relativeMayerVietoris_boundary_sum (n : ℕ) :
    relativeMayerVietorisBoundary U V A hU hV hcover n ≫
      (relativeMayerVietorisSumSequence U V A n).f = 0 := by
  exact comp_zero_of_iso
    (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1))
    (relativeCoverLeftHomologyIso U V A n)
    (relativeCoverMiddleHomologyIso U V A n) _ _ _ _
    ((relativeOpenCoverHomologyIso U V A hU hV hcover (n+1)).hom_inv_id_assoc _)
    (relativeCoverLeftHomologyIso_map U V A n)
    ((relativeCoverChainSequence_shortExact U V A).δ_comp (n+1) n rfl)

theorem relativeMayerVietoris_exact_at_intersection (n : ℕ) :
    (ShortComplex.mk _ _ (relativeMayerVietoris_boundary_sum U V A hU hV hcover n)).Exact := by
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1))
      (relativeCoverLeftHomologyIso U V A n) (relativeCoverMiddleHomologyIso U V A n)
      ?_ (relativeCoverLeftHomologyIso_map U V A n))
    ((relativeCoverChainSequence_shortExact U V A).homology_exact₁ (n+1) n rfl)
  exact (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1)).hom_inv_id_assoc _

include hU hV hcover

/-- Vanishing criterion in full relative singular homology, suitable for
inductively joining bundle charts. -/
theorem relativeOpenCover_isZero (n : ℕ)
    (hu : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1)))
    (hv : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1)))
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n)) :
    IsZero (relativeSingularHomology (subspaceInclusion A) (n+1)) := by
  have hg : (relativeMayerVietorisSumSequence U V A (n+1)).g = 0 := by
    dsimp only [relativeMayerVietorisSumSequence]
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
    · exact hu.eq_of_src _ _
    · exact hv.eq_of_src _ _
  exact (relativeMayerVietoris_exact_at_relative U V A hU hV hcover n).isZero_of_both_zeros
    hg (hi.eq_of_tgt _ _)

/-- Agreement on the two charts determines a global normalization uniquely
when the preceding overlap group vanishes. -/
theorem relativeOpenCover_hom_ext (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z)
    (hu : restrictedPairToAmbientHomologyMap U A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap U A (n+1) ≫ g)
    (hv : restrictedPairToAmbientHomologyMap V A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap V A (n+1) ≫ g) : f = g := by
  have := relativeOpenCover_sum_epi U V A hU hV hcover n hi
  apply (cancel_epi (relativeMayerVietorisSumSequence U V A (n+1)).g).mp
  dsimp only [relativeMayerVietorisSumSequence]
  apply biprod.hom_ext'
  · erw [biprod.inl_desc_assoc, biprod.inl_desc_assoc]
    exact hu
  · erw [biprod.inr_desc_assoc, biprod.inr_desc_assoc]
    exact hv

end

end Kaplansky

end

end OAI
