import OAI.Computability.PerfectCompleteness.Algebra.BilinearWitnessLemmas
import OAI.Computability.PerfectCompleteness.Construction.ChildUnmarkedSpace
import OAI.Computability.PerfectCompleteness.Construction.ProjectedNodeEmbedding
import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalDecoderTables

namespace OAI

section

namespace PerfectCompleteness.ProjectedNativeCollision

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
  (p : ∀ leaf k, MixedSupport.Projection (slots leaf k) (projected leaf k))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

theorem form_eq_on_pullbacks
    (q0 q1 : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (htarget : DecoderSourcePullback.upperTarget p upper q0 =
      DecoderSourcePullback.upperTarget p upper q1)
    (f g : H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) :
    OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH slots upper level d)
        (HierarchicalLeftDecoder.output slots upper level hbranch d q0)
        (HPullback (ChildBlockProjection.nodeProjection p
          (HierarchicalLeftDecoder.LowerNode upper level d)) f)
        (HPullback (ChildBlockProjection.nodeProjection p
          (HierarchicalLeftDecoder.LowerNode upper level d)) g) =
      OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH slots upper level d)
        (HierarchicalLeftDecoder.output slots upper level hbranch d q1)
        (HPullback (ChildBlockProjection.nodeProjection p
          (HierarchicalLeftDecoder.LowerNode upper level d)) f)
        (HPullback (ChildBlockProjection.nodeProjection p
          (HierarchicalLeftDecoder.LowerNode upper level d)) g) := by
  have h0 := DecoderSourcePullback.form_upperTarget p upper level hbranch d
    (DecoderSourcePullback.selectedCut upper level d) q0 f g
  have h1 := DecoderSourcePullback.form_upperTarget p upper level hbranch d
    (DecoderSourcePullback.selectedCut upper level d) q1 f g
  rw [htarget] at h0
  exact h0.symm.trans h1

theorem decode_eq_some_of_high (s : Nat)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (hhigh : s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q)) :
    HierarchicalDecoderTables.decode slots upper level hbranch d s q =
      some (HierarchicalLeftDecoder.output slots upper level hbranch d q) := by
  exact ite_eq_right (Nat.not_le.mpr hhigh)

theorem two_high_hits_restricted (s : Nat)
    (q0 q1 : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (right : Module.Dual F2 (OwnInputReference.UpperSpace projected upper))
    (hrank0 : s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q0))
    (hrank1 : s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q1))
    (hhit0 : DecoderSourcePullback.upperTarget p upper q0 = right)
    (hhit1 : DecoderSourcePullback.upperTarget p upper q1 = right) :
    BilinearCollisionTransfer.restrictedCollision
      ((HierarchicalDecoderTables.decode slots upper level hbranch d s q0).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)))
      ((HierarchicalDecoderTables.decode slots upper level hbranch d s q1).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)))
      (LinearMap.range (HPullback (ChildBlockProjection.nodeProjection p
        (HierarchicalLeftDecoder.LowerNode upper level d)))) = true := by
  rw [decode_eq_some_of_high upper level hbranch d s q0 hrank0,
    decode_eq_some_of_high upper level hbranch d s q1 hrank1]
  apply decide_eq_true
  refine ⟨_, _, rfl, rfl, ?_⟩
  rintro v ⟨f, rfl⟩ w ⟨g, rfl⟩
  exact form_eq_on_pullbacks p upper level hbranch d q0 q1
    (hhit0.trans hhit1.symm) f g

theorem two_high_hits_restricted_on (s : Nat)
    (q0 q1 : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (right : Module.Dual F2 (OwnInputReference.UpperSpace projected upper))
    (hrank0 : s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q0))
    (hrank1 : s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q1))
    (hhit0 : DecoderSourcePullback.upperTarget p upper q0 = right)
    (hhit1 : DecoderSourcePullback.upperTarget p upper q1 = right)
    (U : Submodule F2 (HierarchicalDecoderTables.LowerH slots upper level d))
    (hU : U ≤ LinearMap.range (HPullback (ChildBlockProjection.nodeProjection p
      (HierarchicalLeftDecoder.LowerNode upper level d)))) :
    BilinearCollisionTransfer.restrictedCollision
      ((HierarchicalDecoderTables.decode slots upper level hbranch d s q0).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)))
      ((HierarchicalDecoderTables.decode slots upper level hbranch d s q1).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d))) U = true := by
  obtain ⟨F, G, hF, hG, hFG⟩ := of_decide_eq_true
    (two_high_hits_restricted p upper level hbranch d s q0 q1 right
      hrank0 hrank1 hhit0 hhit1)
  apply decide_eq_true
  exact ⟨F, G, hF, hG, fun v hv w hw => hFG v (hU hv) w (hU hw)⟩

section SourceKernel

variable {rows : Nat → Nat} {v m k : Nat} {C : Type*} [Fintype C]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch k) → Slots branch k)
  (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
  (raw : (i : Fin (branch k)) →
    SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)

theorem parent_childSlots_of_unmarked (i : Fin (branch k))
    (hi : SourceChildKernel.rawProjected rows clauses designated i (raw i) = false) :
    childSlots (SourceChildKernel.parentRightSlots rows clauses designated sources raw) i =
      childSlots (SourceChildKernel.parentLeftSlots clauses designated sources) i := by
  funext leaf a
  change SourceChildKernel.mixedSlots clauses designated i (sources i)
      (SourceChildKernel.rawProjected rows clauses designated i (raw i)) leaf a =
    SourceChildKernel.nativeSlots clauses designated i (sources i) leaf a
  rw [hi]
  rfl

theorem parent_unmarked_le_range :
    ChildUnmarkedSpace.space
      (SourceChildKernel.parentLeftSlots clauses designated sources)
      (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)) ≤
      LinearMap.range (HPullback
        (SourceChildKernel.parentProjection rows clauses designated sources raw)) := by
  apply ChildUnmarkedSpace.space_le_projected_range
  exact parent_childSlots_of_unmarked clauses designated sources raw

end SourceKernel

end
end PerfectCompleteness.ProjectedNativeCollision

end

end OAI
