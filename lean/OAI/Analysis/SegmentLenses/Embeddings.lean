import OAI.Analysis.SegmentLenses.Components

namespace OAI

/-!
# Segment embeddings and convex tree regions
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


section SegmentEmbeddings
variable {V W : Type*} [decidableEqV : DecidableEq V] [decidableEqW : DecidableEq W] [SegmentSystem V] [SegmentSystem W]



structure SegmentEmbedding where
  toEmbedding : V ↪ W
  map_segment : ∀ S : Finset V, SegmentSystem.isSegment S →
    SegmentSystem.isSegment (S.map toEmbedding)
  preimage_segment : ∀ S : Finset W, SegmentSystem.isSegment S →
    S.preimage toEmbedding toEmbedding.injective.injOn = ∅ ∨
      SegmentSystem.isSegment (S.preimage toEmbedding toEmbedding.injective.injOn)

namespace SegmentEmbedding

def testMap (e : SegmentEmbedding (V := V) (W := W)) : Test V →ₗ[ℝ] Test W where
  toFun u := Test.ofFinsupp (u.coeff.embDomain e.toEmbedding)
  map_add' u v := Finsupp.embDomain_add _ _ _
  map_smul' c u := by
    apply Finsupp.ext
    intro w
    change Finsupp.embDomain e.toEmbedding (c • u.coeff) w = c • Finsupp.embDomain e.toEmbedding u.coeff w
    rw [Finsupp.embDomain_apply, Finsupp.embDomain_apply]
    split_ifs <;> simp

@[simp] theorem testMap_apply (e : SegmentEmbedding (V := V) (W := W)) (u : Test V) (v : V) :
    (e.testMap u).coeff (e.toEmbedding v) = u.coeff v := by
  have _ := decidableEqV
  have _ := decidableEqW
  exact Finsupp.embDomain_apply_self _ _ _

theorem testMap_sum (e : SegmentEmbedding (V := V) (W := W)) (u : Test V) (S : Finset W) :
    ∑ w ∈ S, (e.testMap u).coeff w =
      ∑ v ∈ S.preimage e.toEmbedding e.toEmbedding.injective.injOn, u.coeff v := by
  classical
  have h := Finset.sum_preimage e.toEmbedding S e.toEmbedding.injective.injOn
    (e.testMap u).coeff (fun w _ hn => Finsupp.embDomain_of_notMem_range e.toEmbedding u.coeff w hn)
  simpa only [e.testMap_apply] using h.symm


theorem norm_testMap (e : SegmentEmbedding (V := V) (W := W)) (u : Test V) :
    ‖e.testMap u‖ = ‖u‖ := by
  classical
  apply le_antisymm
  · change segmentSeminorm W (e.testMap u).coeff ≤ _
    rw [segmentSeminorm_apply]
    apply ciSup_le
    intro F
    let pieces : F.sets → Finset V := fun S => S.val.preimage e.toEmbedding e.toEmbedding.injective.injOn
    have hp : ∀ S, pieces S = ∅ ∨ SegmentSystem.isSegment (pieces S) :=
      fun S => e.preimage_segment S.val (F.segment _ S.property)
    have hd : Pairwise fun S T => Disjoint (pieces S) (pieces T) := by
      intro S T hST
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact Finset.disjoint_left.mp (F.disjoint S.property T.property (fun h => hST (Subtype.ext h)))
        (Finset.mem_preimage.mp hv) (Finset.mem_preimage.mp hw)
    have h := indexed_test_bound u.coeff pieces hp hd
    have he : F.seminorm (e.testMap u).coeff ^ 2 = ∑ S, (∑ v ∈ pieces S, u.coeff v)^2 := by
      rw [F.seminorm_sq]
      simp_rw [e.testMap_sum]
      rfl
    rw [← he] at h
    exact (sq_le_sq₀ (apply_nonneg _ _) (norm_nonneg u)).mp h
  · change segmentSeminorm V u.coeff ≤ _
    rw [segmentSeminorm_apply]
    apply ciSup_le
    intro F
    let pieces : F.sets → Finset W := fun S => S.val.map e.toEmbedding
    have hp : ∀ S, pieces S = ∅ ∨ SegmentSystem.isSegment (pieces S) :=
      fun S => Or.inr (e.map_segment S.val (F.segment _ S.property))
    have hd : Pairwise fun S T => Disjoint (pieces S) (pieces T) := by
      intro S T hST
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨v',hv',he⟩ := Finset.mem_map.mp hw'
      have he' := e.toEmbedding.injective he
      subst v'
      exact Finset.disjoint_left.mp (F.disjoint S.property T.property (fun h => hST (Subtype.ext h))) hv hv'
    have h := indexed_test_bound (e.testMap u).coeff pieces hp hd
    have he : F.seminorm u.coeff ^ 2 = ∑ S, (∑ w ∈ pieces S, (e.testMap u).coeff w)^2 := by
      rw [F.seminorm_sq]
      simp only [pieces, Finset.sum_map, e.testMap_apply]
    rw [← he] at h
    exact (sq_le_sq₀ (apply_nonneg _ _) (norm_nonneg (e.testMap u))).mp h

def testIsometry (e : SegmentEmbedding (V := V) (W := W)) : Test V →ₗᵢ[ℝ] Test W :=
  ⟨e.testMap, e.norm_testMap⟩

end SegmentEmbedding
end SegmentEmbeddings


section ConvexTreeEmbeddings
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [PartialOrder V] [PartialOrder W] [LocallyFiniteOrder W]
  [TreeOrder W] [SegmentSystem V] [SegmentSystem W]
  [IntervalSegments V] [IntervalSegments W]



def convexSegmentEmbedding (e : V ↪o W)
    (hc : ∀ {a b w : W}, a ∈ Set.range e → b ∈ Set.range e → a ≤ w → w ≤ b → w ∈ Set.range e) :
    SegmentEmbedding (V := V) (W := W) where
  toEmbedding := e.toEmbedding
  map_segment S hS := by
    obtain ⟨a,b,hab,hs⟩ := (IntervalSegments.iff_interval S).mp hS
    apply (IntervalSegments.iff_interval _).mpr
    refine ⟨e a,e b,e.monotone hab,?_⟩
    intro w
    constructor
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
      exact ⟨e.monotone ((hs v).mp hv).1, e.monotone ((hs v).mp hv).2⟩
    · rintro ⟨haw,hwb⟩
      obtain ⟨v,rfl⟩ := hc ⟨a,rfl⟩ ⟨b,rfl⟩ haw hwb
      exact Finset.mem_map.mpr ⟨v,(hs v).mpr ⟨e.le_iff_le.mp haw,e.le_iff_le.mp hwb⟩,rfl⟩
  preimage_segment S hS := by
    classical
    let T := S.filter (fun w => w ∈ Set.range e)
    have ht : T = ∅ ∨ SegmentSystem.isSegment T := subinterval_isSegment hS (Finset.filter_subset _ _) (by
      intro a ha b hb w haw hwb
      exact Finset.mem_filter.mpr ⟨by
        obtain ⟨l,r,hlr,hs⟩ := (IntervalSegments.iff_interval S).mp hS
        exact (hs w).mpr ⟨((hs a).mp (Finset.mem_filter.mp ha).1).1.trans haw,
          hwb.trans ((hs b).mp (Finset.mem_filter.mp hb).1).2⟩,
        hc (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 haw hwb⟩)
    rcases ht with ht | ht
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hm : e v ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_preimage.mp hv,⟨v,rfl⟩⟩
      rw [ht] at hm
      exact Finset.notMem_empty _ hm
    · right
      obtain ⟨a,b,hab,hs⟩ := (IntervalSegments.iff_interval T).mp ht
      have ha := (hs a).mpr ⟨le_rfl,hab⟩
      have hb := (hs b).mpr ⟨hab,le_rfl⟩
      obtain ⟨a',rfl⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨b',rfl⟩ := (Finset.mem_filter.mp hb).2
      apply (IntervalSegments.iff_interval _).mpr
      refine ⟨a',b',e.le_iff_le.mp hab,?_⟩
      intro v
      rw [Finset.mem_preimage]
      have he : e v ∈ S ↔ e v ∈ T := by simp only [T,Finset.mem_filter]; exact ⟨fun h => ⟨h,⟨v,rfl⟩⟩,And.left⟩
      change e v ∈ S ↔ a' ≤ v ∧ v ≤ b'
      rw [he,hs]
      exact and_congr e.le_iff_le e.le_iff_le

end ConvexTreeEmbeddings



namespace Region
variable {V : Type*}



def Vertex (P : V → Prop) := {v : V // P v}

variable {P : V → Prop} [PartialOrder V]
instance : PartialOrder (Vertex P) := inferInstanceAs (PartialOrder {v : V // P v})
instance [TreeOrder V] : TreeOrder (Vertex P) where
  lower_chain := fun {a b c} hab hbc => TreeOrder.lower_chain (V := V) (a := a.val) (b := b.val) (c := c.val) hab hbc

instance : SegmentSystem (Vertex P) where
  isSegment := IsInterval (· ≤ ·)
  singleton v := by
    refine ⟨v,v,le_rfl,?_⟩
    intro w
    simp only [Finset.mem_singleton]
    exact ⟨fun h => by subst w; exact ⟨le_rfl,le_rfl⟩, fun h => le_antisymm h.2 h.1⟩
instance [TreeOrder V] : IntervalSegments (Vertex P) where
  iff_interval _ := Iff.rfl

instance [LocallyFiniteOrder V] : LocallyFiniteOrder (Vertex P) :=
  LocallyFiniteOrder.ofFiniteIcc (by
    intro a b
    apply Set.Finite.of_injOn (f := fun v : Vertex P => v.val) (t := Set.Icc a.val b.val)
    · intro v hv; exact hv
    · exact fun _ _ _ _ h => Subtype.ext h
    · exact Set.finite_Icc _ _)

instance [LocallyFiniteOrderBot V] : LocallyFiniteOrderBot (Vertex P) := by
  classical
  have hf : ∀ b : Vertex P, {v : Vertex P | v ≤ b}.Finite := by
    intro b
    apply Set.Finite.of_injOn (f := fun v : Vertex P => v.val) (t := Set.Iic b.val)
    · intro v hv; exact hv
    · exact fun _ _ _ _ h => Subtype.ext h
    · exact Set.finite_Iic _
  exact LocallyFiniteOrderBot.ofIic (Vertex P) (fun b => (hf b).toFinset) (fun a x => by simp)

instance [Countable V] : Countable (Vertex P) := by unfold Vertex; infer_instance

def inclusion : Vertex P ↪o V where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

@[simp] theorem range_inclusion : Set.range (inclusion (P := P)) = {v | P v} := by
  ext v
  exact ⟨fun ⟨w,h⟩ => h ▸ w.property, fun hv => ⟨⟨v,hv⟩,rfl⟩⟩

variable [DecidableEq V] [LocallyFiniteOrder V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]
local instance : DecidableEq (Vertex P) := Classical.decEq _

def embedding (hc : ∀ a b v, P a → P b → a ≤ v → v ≤ b → P v) :
    SegmentEmbedding (V := Vertex P) (W := V) :=
  convexSegmentEmbedding inclusion (by
    intro a b w ha hb haw hwb
    rw [range_inclusion] at ha hb ⊢
    exact hc a b w ha hb haw hwb)

end Region

namespace SegmentEmbedding
variable {V W : Type*} [DecidableEq V] [DecidableEq W] [SegmentSystem V] [SegmentSystem W]

def primalMap (e : SegmentEmbedding (V := V) (W := W)) : Primal V →L[ℝ] Primal W :=
  ((UniformSpace.Completion.toComplL : Test W →L[ℝ] Primal W).comp e.testIsometry.toContinuousLinearMap).extend
    UniformSpace.Completion.toComplL

@[simp] theorem primalMap_test (e : SegmentEmbedding (V := V) (W := W)) (u : Test V) :
    e.primalMap (u : Primal V) = (e.testMap u : Primal W) :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) u

@[simp] theorem norm_primalMap (e : SegmentEmbedding (V := V) (W := W)) (x : Primal V) :
    ‖e.primalMap x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (e.primalMap.continuous.norm) continuous_norm) ?_
  intro u
  rw [e.primalMap_test, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe, e.norm_testMap]

def primalIsometry (e : SegmentEmbedding (V := V) (W := W)) : Primal V →ₗᵢ[ℝ] Primal W :=
  ⟨e.primalMap.toLinearMap, e.norm_primalMap⟩

theorem primalMap_unitVector (e : SegmentEmbedding (V := V) (W := W)) (v : V) :
    e.primalMap (unitVector v) = unitVector (e.toEmbedding v) := by
  rw [unitVector, e.primalMap_test]
  congr 1
  change Finsupp.embDomain e.toEmbedding (Finsupp.single v 1) = Finsupp.single (e.toEmbedding v) 1
  exact Finsupp.embDomain_single _ _ _

end SegmentEmbedding



end SegmentLenses

end

end OAI
