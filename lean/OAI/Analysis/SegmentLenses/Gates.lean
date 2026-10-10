import OAI.Analysis.SegmentLenses.Identifications

namespace OAI

/-!
# Exterior gates and disjoint cone regions
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

section ExteriorGates
variable {V : Type*} [DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]



theorem exists_gate_below (H : Finset V) {v : V} (hv : v ∉ H) :
    ∃ g, Gate H g ∧ g ≤ v := by
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  classical
  let S := Finset.Iic v \ H
  obtain ⟨g,hg,hmin⟩ := Finset.exists_minimal (s := S)
    (show S.Nonempty from ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_Iic.mpr le_rfl,hv⟩⟩)
  have hgS := Finset.mem_sdiff.mp hg
  refine ⟨g,⟨hgS.2,?_⟩,Finset.mem_Iic.mp hgS.1⟩
  intro w hw
  by_contra hn
  have hwS : w ∈ S := Finset.mem_sdiff.mpr
    ⟨Finset.mem_Iic.mpr (hw.le.trans (Finset.mem_Iic.mp hgS.1)),hn⟩
  exact (not_le_of_gt hw) (hmin hwS hw.le)

theorem gate_below_unique {H : Finset V} {g k v : V} (hg : Gate H g) (hk : Gate H k)
    (hgv : g ≤ v) (hkv : k ≤ v) : g=k := by
  have _ := locallyFiniteOrderBotV
  rcases TreeOrder.lower_chain hgv hkv with h | h
  · exact gates_incomparable hg hk h
  · exact (gates_incomparable hk hg h).symm

abbrev ExteriorVertex (H : Finset V) := Region.Vertex (fun v => v ∉ H)
local instance (H : Finset V) : DecidableEq (ExteriorVertex H) := Classical.decEq _

def exteriorGate (H : Finset V) (v : ExteriorVertex H) : {g // Gate H g} :=
  ⟨(exists_gate_below H v.property).choose,(exists_gate_below H v.property).choose_spec.1⟩

theorem exteriorGate_le (H : Finset V) (v : ExteriorVertex H) :
    (exteriorGate H v).val ≤ v.val := (exists_gate_below H v.property).choose_spec.2

def exteriorPartition (H : Finset V) : ComponentPartition (V := ExteriorVertex H) (I := {g // Gate H g}) where
  index := exteriorGate H
  comparable := by
    intro v w hvw
    apply Subtype.ext
    exact gate_below_unique (exteriorGate H v).property (exteriorGate H w).property
      ((exteriorGate_le H v).trans hvw) (exteriorGate_le H w)


theorem exteriorGate_eq_iff (H : Finset V) (v : ExteriorVertex H) (g : {g // Gate H g}) :
    exteriorGate H v = g ↔ g.val ≤ v.val := by
  constructor
  · intro he; rw [← he]; exact exteriorGate_le H v
  · intro hgv
    apply Subtype.ext
    exact gate_below_unique (exteriorGate H v).property g.property (exteriorGate_le H v) hgv

def exteriorEmbedding (H : Finset V) (hH : Ancestral (· ≤ ·) H) :
    SegmentEmbedding (V := ExteriorVertex H) (W := V) :=
  Region.embedding (fun _a _b _v ha _hb hav _hvb hv => ha (hH hv hav))

@[simp] theorem exteriorEmbedding_range (H : Finset V) (hH : Ancestral (· ≤ ·) H) :
    Set.range (exteriorEmbedding H hH).toEmbedding = {v | v ∉ H} := by
  have _ := locallyFiniteOrderBotV
  exact
    Region.range_inclusion

theorem exterior_testTail (H : Finset V) (hH : Ancestral (· ≤ ·) H) (u : Test V) :
    (exteriorEmbedding H hH).testMap ((exteriorEmbedding H hH).testRestriction u) =
      Test.ofFinsupp (u.coeff.filter (· ∉ H)) := by
  classical
  apply Finsupp.ext
  intro v
  change ((exteriorEmbedding H hH).testMap ((exteriorEmbedding H hH).testRestriction u)).coeff v =
    (u.coeff.filter (· ∉ H)) v
  rw [Finsupp.filter_apply]
  by_cases hv : v ∉ H
  · rw [ite_eq_left hv]
    exact (exteriorEmbedding H hH).testMap_apply _ (⟨v,hv⟩ : ExteriorVertex H)
  · rw [ite_eq_right hv]
    apply Finsupp.embDomain_of_notMem_range
    simpa only [exteriorEmbedding_range, Set.mem_ofPred_eq] using hv

theorem exterior_primalTail (H : Finset V) (hH : Ancestral (· ≤ ·) H) (x : Primal V) :
    (exteriorEmbedding H hH).primalMap ((exteriorEmbedding H hH).primalRestriction x) = primalTail H x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((exteriorEmbedding H hH).primalMap.continuous.comp
      (exteriorEmbedding H hH).primalRestriction.continuous) (primalTail H).continuous) ?_
  intro u
  rw [SegmentEmbedding.primalRestriction_test,SegmentEmbedding.primalMap_test,
    exterior_testTail,primalTail_test]

theorem primalTail_exterior (H : Finset V) (hH : Ancestral (· ≤ ·) H) (x : Primal (ExteriorVertex H)) :
    primalTail H ((exteriorEmbedding H hH).primalMap x) = (exteriorEmbedding H hH).primalMap x := by
  rw [← exterior_primalTail H hH, SegmentEmbedding.primalRestriction_primalMap]


def exteriorDual (H : Finset V) (hH : Ancestral (· ≤ ·) H) (z : FullDual V) : FullDual (ExteriorVertex H) :=
  z.comp (exteriorEmbedding H hH).primalMap



theorem norm_exteriorDual (H : Finset V) (hH : Ancestral (· ≤ ·) H) (z : FullDual V) :
    ‖exteriorDual H hH z‖ = ‖tail H z‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    have he : exteriorDual H hH z u = tail H z ((exteriorEmbedding H hH).primalMap u) := by
      rw [tail_adjoint,primalTail_exterior]
      rfl
    rw [he]
    simpa only [SegmentEmbedding.norm_primalMap] using
      (tail H z).le_opNorm ((exteriorEmbedding H hH).primalMap u)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    rw [tail_adjoint,← exterior_primalTail H hH u]
    have h := (exteriorDual H hH z).le_opNorm ((exteriorEmbedding H hH).primalRestriction u)
    exact h.trans (mul_le_mul_of_nonneg_left
      ((exteriorEmbedding H hH).norm_primalRestriction_le u) (norm_nonneg _))

end ExteriorGates



end SegmentLenses

end

end OAI
