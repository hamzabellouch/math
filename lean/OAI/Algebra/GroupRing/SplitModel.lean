import Mathlib
import OAI.Algebra.GroupRing.Basic
import OAI.Algebra.GroupRing.AbsorbCells
import OAI.Algebra.GroupRing.VertexCollapse
import OAI.Algebra.GroupRing.RelationSplit

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SplitModel
open Set Topology GroupRingTopology GroupRingTopology.Attachment
variable {G S Q : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (s : S→G) (w : Q→FreeGroup S) (hw : ∀i,FreeGroup.lift s (w i)=1)
  (hs : Function.Surjective (FreeGroup.lift s))
  (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure (Set.range w))
  (L : CellModule.Module G S→+CellModule.Module G Q)
  (hL : ∀g i,L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i)))=Finsupp.single (g,i) 1)
include hs hker hL in
theorem contractible : ContractibleSpace (IndexedCells.Cover s w hw) := by
  let := IndexedCells.cover_simplyConnected s w hw hs hker
  let a := IndexedCells.attaching s w hw
  let f : C(IndexedCells.Cover s w hw,IndexedCells.Cover s w hw) := .id _
  let y := IndexedCells.inclusion s w hw (Cayley.vertex s 1)
  let f' := VertexCollapse.map s a f y
  have hv : ∀g,f' (IndexedCells.inclusion s w hw (Cayley.vertex s g))=y :=
    VertexCollapse.map_vertex s a f y
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨y,⟨(VertexCollapse.homotopy s a f y).trans (AbsorbCells.homotopy s w hw L hL f' y hv)⟩⟩
include hw hs hker hL in
theorem has_model [Finite S] [Finite Q] [Nonempty Q] : HasFiniteTwoDimensionalClassifyingSpace G := by
  let a := IndexedCells.attaching s w hw
  refine ⟨IndexedCells.Base s w hw,inferInstance,inferInstance,inferInstance,inferInstance,
    CellPresentation.base_finite s a,CellPresentation.base_no_higher s a,
    CellPresentation.base_two_cell s a,CellPresentation.basePoint s a,
    ⟨CellPresentation.fundamentalEquiv s a w (IndexedCells.wordLift_rel s w hw) hs hker⟩,
    IndexedCells.Cover s w hw,inferInstance,contractible s w hw hs hker L hL,
    CellPresentation.projection s a,?_,?_⟩
  · exact (CellPresentation.projection_quotient s a).isCoveringMap
  · exact (CellPresentation.projection_quotient s a).surjective
end TorsionFreeZeroDivisors.SplitModel

namespace TorsionFreeZeroDivisors.RelationModel
open AlgebraicPictures RelationArea
variable {A I : Type} (rel : I→List (A×Bool))
  (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0)
local instance : TopologicalSpace (G rel) := ⊥
local instance : DiscreteTopology (G rel) := ⟨rfl⟩
def generators : A→G rel := PresentedGroup.of
lemma lift_generators : FreeGroup.lift (generators rel)=q rel := by ext a;rfl
include hz in
theorem has_model [Finite A] [Finite I] [Nonempty I] : HasFiniteTwoDimensionalClassifyingSpace (G rel) := by
  apply SplitModel.has_model (generators rel) (fun i=>FreeGroup.mk (rel i))
    (fun i=>by rw [lift_generators];exact q_rel rel i)
    (by rw [lift_generators];exact PresentedGroup.mk_surjective _)
    (by rw [lift_generators];exact QuotientGroup.ker_mk' _)
    (RelationSplit.retract rel)
  intro g i
  rw [lift_generators]
  have h:=RelationSplit.retract_d₂_single rel hz g i
  simpa only [RelationArea.d₂_single,one_zsmul] using h
end TorsionFreeZeroDivisors.RelationModel

end

end OAI
