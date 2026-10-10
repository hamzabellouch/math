import OAI.AlgebraicTopology.IntegralHomology.Equivalence
import OAI.AlgebraicTopology.IntegralHomology.Quotient
import OAI.AlgebraicTopology.IntegralHomology.SmallChains

namespace OAI

noncomputable section

namespace Kaplansky

/-! Small relative excision, Mayer-Vietoris, and naturality. -/

section
open CategoryTheory Limits AlgebraicTopology

section
variable {X : Type} [TopologicalSpace X]

/-- Inclusion between subspaces of the same ambient space. -/
def subspaceInclusionOfLE {U V : Set X} (h : U ⊆ V) :
    TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

instance {U V : Set X} (h : U ⊆ V) : Mono (subspaceInclusionOfLE h) := by
  apply (TopCat.mono_iff_injective _).mpr
  intro a b he
  exact Subtype.ext (congrArg (fun z : V => z.val) he)

@[reassoc (attr := simp)]
theorem subspaceInclusionOfLE_comp {U V : Set X} (h : U ⊆ V) :
    subspaceInclusionOfLE h ≫ subspaceInclusion V = subspaceInclusion U := rfl

theorem singularSubsetIso_naturality {U V : Set X} (h : U ⊆ V) :
    (singularSubsetIso U).hom ≫ SSet.Subcomplex.homOfLE (singularSubset_mono h) =
      TopCat.toSSet.map (subspaceInclusionOfLE h) ≫ (singularSubsetIso V).hom := by
  apply (cancel_mono (singularSubset V).ι).mp
  simp [← Functor.map_comp, Category.assoc]

def singularIntersectionIso (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)) ≅ (singularSubset U ⊓ singularSubset V).toSSet :=
  singularSubsetIso (U ∩ V) ≪≫ SSet.Subcomplex.eqToIso (singularSubset_inter U V)

theorem singularIntersectionIso_left (U V : Set X) :
    (singularIntersectionIso U V).hom ≫ SSet.Subcomplex.homOfLE inf_le_left =
      TopCat.toSSet.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) ≫
        (singularSubsetIso U).hom := by
  apply (cancel_mono (singularSubset U).ι).mp
  simp [singularIntersectionIso, Category.assoc, ← Functor.map_comp]

theorem singularIntersectionIso_right (U V : Set X) :
    (singularIntersectionIso U V).hom ≫ SSet.Subcomplex.homOfLE inf_le_right =
      TopCat.toSSet.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V)) ≫
        (singularSubsetIso V).hom := by
  apply (cancel_mono (singularSubset V).ι).mp
  simp [singularIntersectionIso, Category.assoc, ← Functor.map_comp]

def singularIntoSmallLeft (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ smallSingularSet U V :=
  (singularSubsetIso U).hom ≫ SSet.Subcomplex.homOfLE le_sup_left

def singularIntoSmallRight (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of V) ⟶ smallSingularSet U V :=
  (singularSubsetIso V).hom ≫ SSet.Subcomplex.homOfLE le_sup_right

theorem smallSingularSet_isPushout (U V : Set X) :
    IsPushout
      (TopCat.toSSet.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.toSSet.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V)))
      (singularIntoSmallLeft U V) (singularIntoSmallRight U V) := by
  have h := SSet.Subcomplex.BicartSq.isPushout
    (X := TopCat.toSSet.obj (TopCat.of X))
    (A₁ := singularSubset U ⊓ singularSubset V)
    (A₂ := singularSubset U) (A₃ := singularSubset V)
    (A₄ := singularSubset U ⊔ singularSubset V) { sup_eq := rfl, inf_eq := rfl }
  exact h.of_iso' (singularIntersectionIso U V) (singularSubsetIso U)
    (singularSubsetIso V) (Iso.refl _) (singularIntersectionIso_left U V)
    (singularIntersectionIso_right U V) (Category.comp_id (singularIntoSmallLeft U V)).symm
    (Category.comp_id (singularIntoSmallRight U V)).symm

def singularChainsIntoSmallLeft (U V : Set X) :
    integralSingularChains.obj (TopCat.of U) ⟶ smallSingularChains U V :=
  integralSimplicialChains.map (singularIntoSmallLeft U V)

def singularChainsIntoSmallRight (U V : Set X) :
    integralSingularChains.obj (TopCat.of V) ⟶ smallSingularChains U V :=
  integralSimplicialChains.map (singularIntoSmallRight U V)

@[reassoc (attr := simp)]
theorem singularChainsIntoSmallLeft_inclusion (U V : Set X) :
    singularChainsIntoSmallLeft U V ≫ smallSingularChainInclusion U V =
      integralSingularChains.map (subspaceInclusion U) := by
  change integralSimplicialChains.map _ ≫ integralSimplicialChains.map _ = _
  erw [← Functor.map_comp]
  simp [singularIntoSmallLeft]
  rfl

@[reassoc (attr := simp)]
theorem singularChainsIntoSmallRight_inclusion (U V : Set X) :
    singularChainsIntoSmallRight U V ≫ smallSingularChainInclusion U V =
      integralSingularChains.map (subspaceInclusion V) := by
  change integralSimplicialChains.map _ ≫ integralSimplicialChains.map _ = _
  erw [← Functor.map_comp]
  simp [singularIntoSmallRight]
  rfl

theorem smallSingularChains_isPushout (U V : Set X) :
    IsPushout
      (integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)))
      (integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V)))
      (singularChainsIntoSmallLeft U V) (singularChainsIntoSmallRight U V) :=
  integralSimplicialChains.map_isPushout (smallSingularSet_isPushout U V)

/-- Mayer–Vietoris chain sequence for genuine subspaces, with the complex
of small chains at the right. No open-cover comparison is assumed. -/
def smallMayerVietorisSequence (U V : Set X) :=
  (smallSingularChains_isPushout U V).shortComplex

theorem smallMayerVietorisSequence_shortExact (U V : Set X) :
    (smallMayerVietorisSequence U V).ShortExact := by
  have hm₁ : Mono (integralSingularChains.map
      (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U))) := by
    unfold integralSingularChains
    infer_instance
  have hm : Mono (smallMayerVietorisSequence U V).f := by
    exact @biprod.mono_lift_of_mono_left _ _ _ _ _ _ _ _ _ hm₁
  have he : Epi (smallMayerVietorisSequence U V).g :=
    (smallSingularChains_isPushout U V).epi_shortComplex_g
  exact { exact := (smallSingularChains_isPushout U V).exact_shortComplex }

def smallMayerVietorisBoundary (U V : Set X) (n : ℕ) :
    (smallSingularChains U V).homology (n+1) ⟶
      (integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)) :=
  (smallMayerVietorisSequence_shortExact U V).δ (n+1) n rfl

theorem smallMayerVietoris_exact (U V : Set X) (n : ℕ) :
    (ShortComplex.mk _ _
      ((smallMayerVietorisSequence_shortExact U V).comp_δ (n+1) n rfl)).Exact :=
  (smallMayerVietorisSequence_shortExact U V).homology_exact₃ (n+1) n rfl

end

variable {X : Type} [TopologicalSpace X]
  {U₀ V₀ U V : Set X}

def smallSingularChainsMap (hU : U₀ ⊆ U) (hV : V₀ ⊆ V) :
    smallSingularChains U₀ V₀ ⟶ smallSingularChains U V :=
  integralSimplicialChains.map (SSet.Subcomplex.homOfLE
    (sup_le_sup (singularSubset_mono hU) (singularSubset_mono hV)))

instance (hU : U₀ ⊆ U) (hV : V₀ ⊆ V) : Mono (smallSingularChainsMap hU hV) := by
  exact integralSimplicialChains.map_mono (SSet.Subcomplex.homOfLE
    (sup_le_sup (singularSubset_mono hU) (singularSubset_mono hV)))

@[reassoc (attr := simp)]
theorem smallSingularChainsMap_inclusion (hU : U₀ ⊆ U) (hV : V₀ ⊆ V) :
    smallSingularChainsMap hU hV ≫ smallSingularChainInclusion U V =
      smallSingularChainInclusion U₀ V₀ := by
  unfold smallSingularChainsMap smallSingularChainInclusion
  erw [← Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem singularChainsIntoSmallLeft_map (hU : U₀ ⊆ U) (hV : V₀ ⊆ V) :
    singularChainsIntoSmallLeft U₀ V₀ ≫ smallSingularChainsMap hU hV =
      integralSingularChains.map (subspaceInclusionOfLE hU) ≫
        singularChainsIntoSmallLeft U V := by
  apply (cancel_mono (smallSingularChainInclusion U V)).mp
  simp [Category.assoc, ← Functor.map_comp]

@[reassoc (attr := simp)]
theorem singularChainsIntoSmallRight_map (hU : U₀ ⊆ U) (hV : V₀ ⊆ V) :
    singularChainsIntoSmallRight U₀ V₀ ≫ smallSingularChainsMap hU hV =
      integralSingularChains.map (subspaceInclusionOfLE hV) ≫
        singularChainsIntoSmallRight U V := by
  apply (cancel_mono (smallSingularChainInclusion U V)).mp
  simp [Category.assoc, ← Functor.map_comp]

/-- Naturality of the actual small-chain gluing sequence under inclusions
of both members of the cover. -/
def smallMayerVietorisSequenceMap (hU : U₀ ⊆ U) (hV : V₀ ⊆ V) :
    smallMayerVietorisSequence U₀ V₀ ⟶ smallMayerVietorisSequence U V where
  τ₁ := integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_inter hU hV))
  τ₂ := biprod.map (integralSingularChains.map (subspaceInclusionOfLE hU))
    (integralSingularChains.map (subspaceInclusionOfLE hV))
  τ₃ := smallSingularChainsMap hU hV
  comm₁₂ := by
    apply biprod.hom_ext <;>
      simp [smallMayerVietorisSequence, CommSq.shortComplex, Category.assoc,
        ← Functor.map_comp] <;> rfl
  comm₂₃ := by
    apply biprod.hom_ext' <;>
      simp [smallMayerVietorisSequence, CommSq.shortComplex]

/-- Relative Mayer–Vietoris at chain level. The removed set is restricted
to each chart and to their intersection; at the right it uses small chains
in the removed subspace. Comparison with full chains is a separate theorem. -/
def smallRelativeMayerVietorisSequence (U V A : Set X) :=
  quotientShortComplex (smallMayerVietorisSequenceMap
    (Set.inter_subset_left : U ∩ A ⊆ U) (Set.inter_subset_left : V ∩ A ⊆ V))

theorem smallRelativeMayerVietorisSequence_shortExact (U V A : Set X) :
    (smallRelativeMayerVietorisSequence U V A).ShortExact := by
  have : Mono (smallMayerVietorisSequenceMap
      (Set.inter_subset_left : U ∩ A ⊆ U)
      (Set.inter_subset_left : V ∩ A ⊆ V)).τ₃ := by
    change Mono (smallSingularChainsMap (Set.inter_subset_left : U ∩ A ⊆ U)
      (Set.inter_subset_left : V ∩ A ⊆ V))
    infer_instance
  exact quotientShortComplex_shortExact _
    (smallMayerVietorisSequence_shortExact _ _)
    (smallMayerVietorisSequence_shortExact _ _)

end

section
open CategoryTheory Limits
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Small relative chains modulo the full chains of the second subspace. -/
def smallRelativeChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (singularChainsIntoSmallRight U V)

/-- Actual chain-level excision into small relative chains. This needs no
openness or covering hypothesis because the target only uses small simplices. -/
def smallRelativeExcisionIso :
    relativeSingularChains (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) ≅
      smallRelativeChains U V := by
  let sq := smallSingularChains_isPushout U V
  haveI := isIso_cokernel_map_of_isPushout sq
  let e := asIso (cokernel.map _ _ _ _ sq.w)
  exact e

/-- Comparison with the full relative chains of (X,V). -/
def smallRelativeComparison : smallRelativeChains U V ⟶
    relativeSingularChains (subspaceInclusion V) :=
  cokernel.map _ _ (𝟙 _) (smallSingularChainInclusion U V)
    (by simp)

/-- The composition of small excision and comparison is exactly the map
induced by the inclusions of pairs (U,U∩V) → (X,V). -/
theorem smallRelativeExcision_comparison :
    (smallRelativeExcisionIso U V).hom ≫ smallRelativeComparison U V =
      relativeChainMap
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U))
        (subspaceInclusion V)
        (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V))
        (subspaceInclusion U) (by rfl) := by
  apply (cancel_epi (cokernel.π (integralSingularChains.map
    (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U))))).mp
  dsimp only [smallRelativeExcisionIso, smallRelativeComparison, relativeChainMap, asIso_hom]
  erw [cokernel.π_desc_assoc, cokernel.π_desc]
  erw [Category.assoc, cokernel.π_desc]
  erw [← Category.assoc, singularChainsIntoSmallLeft_inclusion]
  rfl

def smallRelativeHomologyIso (n : ℕ) :
    relativeSingularHomology
      (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) n ≅
      (smallRelativeChains U V).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (smallRelativeExcisionIso U V)

instance : Mono (singularChainsIntoSmallRight U V) := by
  have : Mono (integralSingularChains.map (subspaceInclusion V)) := by
    unfold integralSingularChains
    infer_instance
  exact mono_of_mono_fac (singularChainsIntoSmallRight_inclusion U V)

def smallRelativeSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (singularChainsIntoSmallRight U V)
    (cokernel.π _) (cokernel.condition _)

theorem smallRelativeSequence_shortExact : (smallRelativeSequence U V).ShortExact := by
  change (ShortComplex.mk (singularChainsIntoSmallRight U V)
    (cokernel.π _) (cokernel.condition _)).ShortExact
  exact { exact := ShortComplex.exact_cokernel _ }

def smallRelativeSequenceComparison :
    smallRelativeSequence U V ⟶ relativeChainSequence (subspaceInclusion V) where
  τ₁ := 𝟙 _
  τ₂ := smallSingularChainInclusion U V
  τ₃ := smallRelativeComparison U V
  comm₁₂ := by simp [smallRelativeSequence, relativeChainSequence]
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- The purely homological step in singular excision. Its explicit premise
is the small-chain theorem, which still requires subdivision for open covers. -/
theorem smallRelativeComparison_quasiIso
    (h : QuasiIso (smallSingularChainInclusion U V)) :
    QuasiIso (smallRelativeComparison U V) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (smallRelativeSequenceComparison U V) (smallRelativeSequence_shortExact U V)
    (relativeChainSequence_shortExact (subspaceInclusion V)) (by
      exact inferInstanceAs (QuasiIso (𝟙 (integralSingularChains.obj (TopCat.of V))))) h

/-- The resulting isomorphism acts on the original relative singular map,
not a proposition introduced to stand for excision. -/
theorem relativeInclusion_isIso_of_smallChains
    (h : QuasiIso (smallSingularChainInclusion U V)) (n : ℕ) :
    IsIso (relativeHomologyMap
      (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U))
      (subspaceInclusion V)
      (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V))
      (subspaceInclusion U) (by rfl) n) := by
  have hq := smallRelativeComparison_quasiIso U V h
  have hi : IsIso (HomologicalComplex.homologyMap (smallRelativeComparison U V) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp
      ((quasiIso_iff _).mp hq n)
  have he : IsIso (HomologicalComplex.homologyMap (smallRelativeExcisionIso U V).hom n) :=
    (smallRelativeHomologyIso U V n).isIso_hom
  unfold relativeHomologyMap
  rw [← smallRelativeExcision_comparison, HomologicalComplex.homologyMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ he hi

end

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Exactness at the intersection term of the actual small-chain sequence. -/
theorem smallMayerVietoris_exact_at_intersection (n : ℕ) :
    (ShortComplex.mk _ _
      ((smallMayerVietorisSequence_shortExact U V).δ_comp (n+1) n rfl)).Exact :=
  (smallMayerVietorisSequence_shortExact U V).homology_exact₁ (n+1) n rfl

/-- Exactness at the homology of the sum of the two subspace complexes. -/
theorem smallMayerVietoris_exact_at_sum (n : ℕ) :
    ((smallMayerVietorisSequence U V).map
      (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)).Exact :=
  (smallMayerVietorisSequence_shortExact U V).homology_exact₂ n

theorem homology_biprod_isZero (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (hC : IsZero (C.homology n)) (hD : IsZero (D.homology n)) :
    IsZero ((C ⊞ D).homology n) := by
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  have hfst : F.map (biprod.fst : C ⊞ D ⟶ C) = 0 := hC.eq_of_tgt _ _
  have hsnd : F.map (biprod.snd : C ⊞ D ⟶ D) = 0 := hD.eq_of_tgt _ _
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (F.obj (C ⊞ D)) = 0
  rw [← F.map_id, ← biprod.total, F.map_add, F.map_comp, F.map_comp,
    hfst, hsnd, zero_comp, zero_comp, add_zero]

theorem smallMayerVietoris_sum_isZero [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0) :
    IsZero ((smallMayerVietorisSequence U V).X₂.homology n) :=
  homology_biprod_isZero _ _ n
    (integralSingularHomology_isZero_contractible U n hn)
    (integralSingularHomology_isZero_contractible V n hn)

/-- For two contractible subspaces, the actual small-chain connecting map
is an isomorphism in degrees at least two. Full singular homology still
requires the small-to-full comparison theorem. -/
def smallMayerVietorisBoundaryIso [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0) :
    (smallSingularChains U V).homology (n+1) ≅
      (integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)) :=
  (smallMayerVietorisSequence_shortExact U V).δIso (n+1) n rfl
    (smallMayerVietoris_sum_isZero U V (n+1) (Nat.succ_ne_zero n))
    (smallMayerVietoris_sum_isZero U V n hn)

theorem smallMayerVietorisBoundaryIso_hom [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0) :
    (smallMayerVietorisBoundaryIso U V n hn).hom = smallMayerVietorisBoundary U V n := rfl

end

open CategoryTheory Limits
section
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (U V : Set X) (U' V' : Set Y) (f : C(X,Y))
  (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')

/-- The induced map on small chains for a continuous map respecting covers.
The construction uses the proved pushout of actual singular-chain complexes. -/
def smallSingularChainsContinuousMap : smallSingularChains U V ⟶ smallSingularChains U' V' :=
  (smallSingularChains_isPushout U V).desc
    (integralSingularChains.map (subspaceMap U U' f hU) ≫ singularChainsIntoSmallLeft U' V')
    (integralSingularChains.map (subspaceMap V V' f hV) ≫ singularChainsIntoSmallRight U' V')
    (by
      apply (cancel_mono (smallSingularChainInclusion U' V')).mp
      simp only [Category.assoc, singularChainsIntoSmallLeft_inclusion,
        singularChainsIntoSmallRight_inclusion, ← Functor.map_comp]
      rfl)

@[reassoc (attr := simp)]
theorem smallSingularChainsContinuousMap_left :
    singularChainsIntoSmallLeft U V ≫ smallSingularChainsContinuousMap U V U' V' f hU hV =
      integralSingularChains.map (subspaceMap U U' f hU) ≫ singularChainsIntoSmallLeft U' V' :=
  (smallSingularChains_isPushout U V).inl_desc _ _ _

@[reassoc (attr := simp)]
theorem smallSingularChainsContinuousMap_right :
    singularChainsIntoSmallRight U V ≫ smallSingularChainsContinuousMap U V U' V' f hU hV =
      integralSingularChains.map (subspaceMap V V' f hV) ≫ singularChainsIntoSmallRight U' V' :=
  (smallSingularChains_isPushout U V).inr_desc _ _ _

@[reassoc (attr := simp)]
theorem smallSingularChainsContinuousMap_inclusion :
    smallSingularChainsContinuousMap U V U' V' f hU hV ≫ smallSingularChainInclusion U' V' =
      smallSingularChainInclusion U V ≫ integralSingularChains.map (TopCat.ofHom f) := by
  apply (smallSingularChains_isPushout U V).hom_ext <;>
    simp [← Functor.map_comp] <;> rfl

theorem smallSingularChainsContinuousMap_mono (hf : Function.Injective f) :
    Mono (smallSingularChainsContinuousMap U V U' V' f hU hV) := by
  have : Mono (TopCat.ofHom f) := (TopCat.mono_iff_injective _).mpr hf
  have : Mono (integralSingularChains.map (TopCat.ofHom f)) := by
    unfold integralSingularChains
    infer_instance
  exact mono_of_mono_fac (smallSingularChainsContinuousMap_inclusion U V U' V' f hU hV)

/-- Naturality includes the intersection term and the signs of the
Mayer–Vietoris differential. -/
def smallMayerVietorisContinuousMap :
    smallMayerVietorisSequence U V ⟶ smallMayerVietorisSequence U' V' where
  τ₁ := integralSingularChains.map
    (subspaceMap (U ∩ V) (U' ∩ V') f (fun _ hx => ⟨hU hx.1, hV hx.2⟩))
  τ₂ := biprod.map (integralSingularChains.map (subspaceMap U U' f hU))
    (integralSingularChains.map (subspaceMap V V' f hV))
  τ₃ := smallSingularChainsContinuousMap U V U' V' f hU hV
  comm₁₂ := by
    apply biprod.hom_ext <;>
      simp [smallMayerVietorisSequence, CommSq.shortComplex, Category.assoc,
        ← Functor.map_comp] <;> rfl
  comm₂₃ := by
    apply biprod.hom_ext' <;>
      simp [smallMayerVietorisSequence, CommSq.shortComplex]

end

end Kaplansky

end

end OAI
