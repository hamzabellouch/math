import OAI.GroupTheory.UniversalGroup.BrownConstruction

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

open Set Metric Topology
namespace UniversalFInfinity.UniverseTransport

section
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
variable {C : Set X} [CWComplex C] {f : X → Y} (hf : IsClosedEmbedding f)

def transportedMap (n : ℕ) (i : RelCWComplex.cell C n) : PartialEquiv (Fin n → ℝ) Y :=
  (RelCWComplex.map n i).trans (hf.isEmbedding.toPartialHomeomorph f).toPartialEquiv

@[simp] lemma transportedMap_apply (n : ℕ) (i : RelCWComplex.cell C n) (x : Fin n → ℝ) :
    transportedMap hf n i x = f (RelCWComplex.map n i x) := rfl

lemma transportedMap_source (n : ℕ) (i : RelCWComplex.cell C n) :
    (transportedMap hf n i).source = ball 0 1 := by
  simp only [transportedMap,PartialEquiv.trans_source,
    IsEmbedding.toPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ,
    RelCWComplex.source_eq]

lemma transportedMap_image (n : ℕ) (i : RelCWComplex.cell C n) (S : Set (Fin n → ℝ)) :
    transportedMap hf n i '' S = f '' (RelCWComplex.map n i '' S) :=
  Set.image_comp f (RelCWComplex.map n i) S

lemma transportedMap_continuousOn (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)

lemma transportedMap_continuousOn_symm (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i).symm (transportedMap hf n i).target := by
  let e := hf.isEmbedding.toPartialHomeomorph f
  change ContinuousOn (fun y => (RelCWComplex.map n i).symm (e.symm y))
    (e.target ∩ e.symm ⁻¹' (RelCWComplex.map n i).target)
  exact (RelCWComplex.continuousOn_symm n i).comp
    (e.continuousOn_symm.mono Set.inter_subset_left) (fun _ h => h.2)

variable [T2Space X]

end

section
open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X] [Nonempty X]
  [CWComplex (univ : Set X)]

abbrev liftMap (n : ℕ) (i : ULift.{v} (RelCWComplex.cell (univ : Set X) n)) :=
  transportedMap (Homeomorph.ulift.symm : X ≃ₜ ULift.{v} X).isClosedEmbedding n i.down

@[instance_reducible]
def liftCW : CWComplex (univ : Set (ULift.{v} X)) where
  cell n := ULift.{v} (RelCWComplex.cell (univ : Set X) n)
  map := liftMap
  source_eq n i := transportedMap_source _ n i.down
  continuousOn n i := transportedMap_continuousOn _ n i.down
  continuousOn_symm n i := transportedMap_continuousOn_symm _ n i.down
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (liftMap p.1 p.2 '' ball 0 1) (liftMap q.1 q.2 '' ball 0 1)
    rw [transportedMap_image,transportedMap_image]
    apply (CWComplex.disjoint_openCell_of_ne ?_).image ULift.up_injective.injOn
      (Set.subset_univ _) (Set.subset_univ _)
    intro h
    apply hpq
    have hf : Function.Injective (fun p : Σ n, ULift.{v} (RelCWComplex.cell (univ : Set X) n) =>
        (⟨p.1,p.2.down⟩ : Σ n, RelCWComplex.cell (univ : Set X) n)) := by
      rintro ⟨n,⟨i⟩⟩ ⟨m,⟨j⟩⟩ h
      cases h
      rfl
    exact hf h
  mapsTo' := by
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n i.down
    refine ⟨fun m => (I m).map ⟨ULift.up,ULift.up_injective⟩,?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n i.down x ∈ CWComplex.cellFrontier n i.down from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hx⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨ULift.up j,Set.mem_iUnion.mpr ⟨Finset.mem_map.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
    rw [transportedMap_image]
    exact ⟨_,hx,rfl⟩
  closed' := by
    intro A _ hclosed
    have hpre : IsClosed (ULift.up ⁻¹' A : Set X) := by
      apply (CWComplex.closed (univ : Set X) _ (Set.subset_univ _)).mpr
      intro n i
      have h := (hclosed n (ULift.up i)).preimage continuous_uliftUp
      rw [transportedMap_image,Set.preimage_inter] at h
      change IsClosed (ULift.up ⁻¹' A ∩ ULift.up ⁻¹'
        (ULift.up '' (RelCWComplex.map n i '' closedBall 0 1))) at h
      rw [Set.preimage_image_eq _ ULift.up_injective] at h
      exact h
    exact ULift.isClosed_iff.mpr hpre
  union' := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro y _
    have hy : y.down ∈ ⋃ n, ⋃ i : RelCWComplex.cell (univ : Set X) n, CWComplex.closedCell n i := by
      rw [CWComplex.union]
      trivial
    simp only [Set.mem_iUnion] at hy
    obtain ⟨n,i,hi⟩ := hy
    refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨ULift.up i,?_⟩⟩
    rw [transportedMap_image]
    exact ⟨y.down,hi,rfl⟩
end
open Set Topology
universe u v
variable {G X E : Type u} [Group G] [TopologicalSpace X] [TopologicalSpace E]
  [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

def liftedCover : ULift.{v} E → ULift.{v} X := fun e => ⟨p e.down⟩
include hp in
lemma liftedCover_quotient : IsQuotientCoveringMap (liftedCover.{u,v} (p := p)) G where
  __ := (Homeomorph.ulift.symm.isQuotientMap.comp hp.toIsQuotientMap).comp
    Homeomorph.ulift.isQuotientMap
  continuous_const_smul g := by
    change Continuous (fun e : ULift.{v} E => ULift.up (g • e.down))
    exact continuous_uliftUp.comp ((hp.continuous_const_smul g).comp continuous_uliftDown)
  apply_eq_iff_mem_orbit := by
    intro e₁ e₂
    change ULift.up (p e₁.down) = ULift.up (p e₂.down) ↔ e₁ ∈ MulAction.orbit G e₂
    rw [ULift.up_inj,hp.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨g,ULift.down_injective hg⟩
    · rintro ⟨g,hg⟩
      exact ⟨g,congrArg ULift.down hg⟩
  disjoint e := by
    obtain ⟨U,hU,hd⟩ := hp.disjoint e.down
    refine ⟨ULift.down ⁻¹' U,continuous_uliftDown.continuousAt.preimage_mem_nhds hU,?_⟩
    rintro g ⟨z,⟨y,hy,hyz⟩,hz⟩
    exact hd g ⟨z.down,⟨y.down,hy,congrArg ULift.down hyz⟩,hz⟩
end UniversalFInfinity.UniverseTransport
namespace UniversalFInfinity.Brown
open Set Topology UniverseTransport
universe z
variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)

include hunif in

theorem geometric_lifted_of_uniform : HasTypeFInfinity (ULift.{z} G) := by
  let : T2Space (ULift.{z} (Base hunif)) := Homeomorph.ulift.symm.t2Space
  let : ContractibleSpace (ULift.{z} (Total hunif)) := Homeomorph.ulift.contractibleSpace
  let q : ULift.{z} (Total hunif) → ULift.{z} (Base hunif) :=
    liftedCover (p := pLimit hunif)
  have hq : IsQuotientCoveringMap q G := liftedCover_quotient (pLimit_covering hunif)
  let : ConnectedSpace (ULift.{z} (Base hunif)) := hq.surjective.connectedSpace hq.continuous
  let cw : CWComplex (univ : Set (ULift.{z} (Base hunif))) := liftCW
  refine ⟨ULift.{z} (Base hunif),inferInstance,inferInstance,inferInstance,cw,?_,?_,?_⟩
  · intro n
    change Finite (ULift.{z} ((baseCW hunif).cell n))
    have := base_finite hunif n
    infer_instance
  · let e : ULift.{z} (Total hunif) := Classical.choice inferInstance
    exact ⟨q e,⟨(hq.fundamentalGroupEquiv ⟨e,rfl⟩).trans
      ((MulEquiv.inv' G).symm.trans MulEquiv.ulift.symm)⟩⟩
  · exact ⟨ULift.{z} (Total hunif),inferInstance,inferInstance,q,hq.surjective,hq.isCoveringMap⟩
end UniversalFInfinity.Brown

end

end OAI
