import OAI.AlgebraicTopology.IntegralHomology.Relative
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace OAI

noncomputable section

namespace Kaplansky

/-! Simplicial gluing, small singular subcomplexes, and cover meshes. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial

section

/-- Integral simplicial chains, using the same free-chain construction as
the preserved integral singular chain complex. -/
def integralSimplicialChains : SSet.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

instance integralSimplicialChains_preservesColimitsOfShape
    (J : Type) [SmallCategory J] : PreservesColimitsOfShape J integralSimplicialChains := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    ((evaluation _ (Type 0)).obj (Opposite.op ⦋n⦌) ⋙
      sigmaConst.obj (ModuleCat.of ℤ ℤ))
  infer_instance

instance integralSimplicialChains_preservesMonomorphisms :
    integralSimplicialChains.PreservesMonomorphisms where
  preserves f _ := by
    unfold integralSimplicialChains
    dsimp [SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono

variable {X : SSet.{0}} (U V : X.Subcomplex)

/-- Chains in a union of subcomplexes form the actual pushout over their
intersection. No topological excision assertion is used. -/
theorem subcomplexChains_isPushout :
    IsPushout
      (integralSimplicialChains.map (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (integralSimplicialChains.map (SSet.Subcomplex.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (integralSimplicialChains.map (SSet.Subcomplex.homOfLE (le_sup_left : U ≤ U ⊔ V)))
      (integralSimplicialChains.map (SSet.Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V))) := by
  apply integralSimplicialChains.map_isPushout
  exact SSet.Subcomplex.BicartSq.isPushout { sup_eq := rfl, inf_eq := rfl }

def subcomplexChainSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  (subcomplexChains_isPushout U V).shortComplex

theorem subcomplexChainSequence_shortExact : (subcomplexChainSequence U V).ShortExact := by
  have hm : Mono (subcomplexChainSequence U V).f := by
    have hm₁ : Mono (integralSimplicialChains.map
        (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U))) :=
      integralSimplicialChains.map_mono _
    exact @biprod.mono_lift_of_mono_left _ _ _ _ _ _ _ _ _ hm₁
  have he : Epi (subcomplexChainSequence U V).g :=
    (subcomplexChains_isPushout U V).epi_shortComplex_g
  exact { exact := (subcomplexChains_isPushout U V).exact_shortComplex }

/-- The chain-level relative excision map for a union of simplicial
subcomplexes. The map is an isomorphism before taking homology. -/
def subcomplexRelativeChainIso :
    cokernel (integralSimplicialChains.map
      (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U))) ≅
    cokernel (integralSimplicialChains.map
      (SSet.Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V))) := by
  let sq := subcomplexChains_isPushout U V
  haveI := isIso_cokernel_map_of_isPushout sq
  exact asIso (cokernel.map _ _ _ _ sq.w)

end

variable {X : Type} [TopologicalSpace X]

def singularSimplexMap (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    C(SimplexCategory.toTop.obj n.unop, X) :=
  (show SimplexCategory.toTop.obj n.unop ⟶ TopCat.of X from σ.down).hom

/-- Singular simplices whose entire image lies in the specified subspace. -/
def singularSubset (U : Set X) : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (subspaceInclusion U))

theorem mem_singularSubset_iff (U : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    σ ∈ (singularSubset U).obj n ↔ ∀ p, singularSimplexMap n σ p ∈ U := by
  constructor
  · rintro ⟨τ, rfl⟩ p
    exact (singularSimplexMap n τ p).property
  · intro h
    refine ⟨ULift.up (TopCat.ofHom ⟨fun p => ⟨singularSimplexMap n σ p, h p⟩,
      (singularSimplexMap n σ).continuous.subtype_mk _⟩), ?_⟩
    rfl

theorem singularSubset_mono {U V : Set X} (h : U ⊆ V) :
    singularSubset U ≤ singularSubset V := by
  intro n σ hσ
  rw [mem_singularSubset_iff] at hσ ⊢
  exact fun p => h (hσ p)

theorem singularSubset_inter (U V : Set X) :
    singularSubset (U ∩ V) = singularSubset U ⊓ singularSubset V := by
  ext n σ
  rw [mem_singularSubset_iff]
  change (∀ p, singularSimplexMap n σ p ∈ U ∩ V) ↔
    σ ∈ (singularSubset U).obj n ∧ σ ∈ (singularSubset V).obj n
  simp only [Set.mem_inter_iff, mem_singularSubset_iff]
  exact forall_and

theorem singularSubset_univ : singularSubset (Set.univ : Set X) = ⊤ := by
  ext n σ
  simp [mem_singularSubset_iff]

/-- Identification with singular simplices of the actual subspace,
including its inherited topology, rather than a replacement chain theory. -/
def singularSubsetIso (U : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ≅ (singularSubset U).toSSet := by
  have : Mono (TopCat.toSSet.map (subspaceInclusion U)) :=
    TopCat.toSSet.map_mono _
  let e := asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (subspaceInclusion U)))
  exact e

@[reassoc (attr := simp)]
theorem singularSubsetIso_hom_ι (U : Set X) :
    (singularSubsetIso U).hom ≫ (singularSubset U).ι =
      TopCat.toSSet.map (subspaceInclusion U) := rfl

def singularSubsetChainsIso (U : Set X) :
    integralSingularChains.obj (TopCat.of U) ≅
      integralSimplicialChains.obj (singularSubset U).toSSet :=
  integralSimplicialChains.mapIso (singularSubsetIso U)

/-- The complex of simplices small for the two-set family. Its simplices
lie wholly in one member, which need not hold for an arbitrary singular simplex. -/
def smallSingularSet (U V : Set X) : SSet.{0} :=
  (singularSubset U ⊔ singularSubset V).toSSet

def smallSingularChains (U V : Set X) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  integralSimplicialChains.obj (smallSingularSet U V)

def smallSingularChainInclusion (U V : Set X) :
    smallSingularChains U V ⟶ integralSingularChains.obj (TopCat.of X) :=
  integralSimplicialChains.map (singularSubset U ⊔ singularSubset V).ι

instance (U V : Set X) : Mono (smallSingularChainInclusion U V) := by
  exact integralSimplicialChains.map_mono (singularSubset U ⊔ singularSubset V).ι

theorem mem_smallSingularSet_iff (U V : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    σ ∈ (singularSubset U ⊔ singularSubset V).obj n ↔
      (∀ p, singularSimplexMap n σ p ∈ U) ∨
      (∀ p, singularSimplexMap n σ p ∈ V) := by
  change (σ ∈ (singularSubset U).obj n ∨ σ ∈ (singularSubset V).obj n) ↔ _
  simp only [mem_singularSubset_iff]

/-- Proven gluing sequence for actual small singular chains. A quasi-isomorphism
from small to full chains is a separate subdivision theorem. -/
def smallSingularChainSequence (U V : Set X) :=
  subcomplexChainSequence (singularSubset U) (singularSubset V)

theorem smallSingularChainSequence_shortExact (U V : Set X) :
    (smallSingularChainSequence U V).ShortExact :=
  subcomplexChainSequence_shortExact _ _

end

open CategoryTheory Topology Filter
section
variable {P X : Type} [PseudoMetricSpace P] [CompactSpace P] [TopologicalSpace X]

/-- A sufficiently small subset of the domain of one singular simplex is
carried into one member of a two-set open cover. -/
theorem continuousMap_cover_mesh (σ : C(P, X)) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ∃ δ > 0, ∀ s : Set P, (∀ a ∈ s, ∀ b ∈ s, dist a b < δ) →
      (∀ a ∈ s, σ a ∈ U) ∨ (∀ a ∈ s, σ a ∈ V) := by
  let c : Bool → Set P := fun b => if b then σ ⁻¹' U else σ ⁻¹' V
  have hc : ∀ b, IsOpen (c b) := by
    intro b
    cases b
    · exact hV.preimage σ.continuous
    · exact hU.preimage σ.continuous
  have hcover : (Set.univ : Set P) ⊆ ⋃ b, c b := by
    intro p _
    have hp : σ p ∈ U ∪ V := by rw [hUV]; trivial
    rcases hp with hp | hp
    · exact Set.mem_iUnion.mpr ⟨true, hp⟩
    · exact Set.mem_iUnion.mpr ⟨false, hp⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcover
  refine ⟨δ, hδ, fun s hs => ?_⟩
  by_cases he : s.Nonempty
  · obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := hball a (Set.mem_univ _)
    have hin : ∀ p ∈ s, p ∈ c b := fun p hp => hb (hs p hp a ha)
    cases b
    · exact Or.inr hin
    · exact Or.inl hin
  · exact Or.inl (fun a ha => (he ⟨a, ha⟩).elim)

/-- A single positive mesh works simultaneously for a finite collection
of continuous simplices, as required for a finite singular chain. -/
theorem finite_continuousMaps_cover_mesh {ι : Type} (F : Finset ι) (σ : ι → C(P, X))
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ∃ δ > 0, ∀ i ∈ F, ∀ s : Set P, (∀ a ∈ s, ∀ b ∈ s, dist a b < δ) →
      (∀ a ∈ s, σ i a ∈ U) ∨ (∀ a ∈ s, σ i a ∈ V) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨δ, hδ, hsmall⟩ := continuousMap_cover_mesh (σ i) U V hU hV hUV
    obtain ⟨ε, hε, hF⟩ := ih
    refine ⟨min δ ε, lt_min hδ hε, fun j hj s hs => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hsmall s (fun a ha b hb => (hs a ha b hb).trans_le (min_le_left _ _))
    · exact hF j hj s (fun a ha b hb => (hs a ha b hb).trans_le (min_le_right _ _))

/-- Geometric decay of mesh supplies one subdivision depth for an entire
finite chain. This proves the compactness/limit step; construction of a
subdivision chain operator with this bound remains separate. -/
theorem finite_continuousMaps_eventually_small {ι : Type} (F : Finset ι)
    (σ : ι → C(P, X)) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (L c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c < 1) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ i ∈ F, ∀ s : Set P,
      (∀ a ∈ s, ∀ b ∈ s, dist a b ≤ L * c ^ k) →
      (∀ a ∈ s, σ i a ∈ U) ∨ (∀ a ∈ s, σ i a ∈ V) := by
  obtain ⟨δ, hδ, hmesh⟩ := finite_continuousMaps_cover_mesh F σ U V hU hV hUV
  have hlim : Tendsto (fun k : ℕ => L * c ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc₀ hc₁).const_mul L
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  exact ⟨N, fun k hk i hi s hs => hmesh i hi s
    (fun a ha b hb => (hs a ha b hb).trans_lt (hN k hk))⟩

open Simplicial
variable {X : Type} [TopologicalSpace X]

instance standardSimplexMetricSpace (Index : Type*) [Fintype Index] :
    MetricSpace (Convexity.StdSimplex ℝ Index) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Index).comapMetricSpace
    (fun simplex => (simplex.weights : Index → ℝ))

/-- The finite mesh estimate applies to the actual standard-simplex
coordinates of the library's singular simplices. -/
theorem singularSimplices_cover_mesh (n : ℕ)
    (F : Finset ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌)))
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ∃ δ > 0, ∀ σ ∈ F, ∀ s : Set (Convexity.StdSimplex ℝ (Fin (n+1))),
      (∀ a ∈ s, ∀ b ∈ s, dist a b < δ) →
      (∀ a ∈ s, TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌) σ a ∈ U) ∨
      (∀ a ∈ s, TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌) σ a ∈ V) :=
  finite_continuousMaps_cover_mesh F (TopCat.toSSetObjEquiv _ _) U V hU hV hUV

end

end Kaplansky

end

end OAI
