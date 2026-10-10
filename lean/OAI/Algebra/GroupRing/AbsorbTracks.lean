import Mathlib
import OAI.Algebra.GroupRing.IndexedCells
import OAI.Algebra.GroupRing.FixedGraph
import OAI.Algebra.GroupRing.GraphLabels

namespace OAI



section
namespace TorsionFreeZeroDivisors.AbsorbTracks
open Set GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
open scoped unitInterval
noncomputable section
variable {G S Q Y : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] [SimplyConnectedSpace Y]
  (s : S→G) (w : Q→FreeGroup S) (hw : ∀i,FreeGroup.lift s (w i)=1)
  (L : CellModule.Module G S→+CellModule.Module G Q)
  (hL : ∀g i,L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i)))=Finsupp.single (g,i) 1)
  (f : C(IndexedCells.Cover s w hw,Y)) (y : Y)
  (hv : ∀g,f (IndexedCells.inclusion s w hw (Cayley.vertex s g))=y)
def graph : C(Cayley.Graph s,Y) := f.comp (IndexedCells.inclusion s w hw)
def initial : (graph s w hw f).Homotopy (.const _ y) := FixedGraph.homotopy s (graph s w hw f) y hv
lemma initial_vertex (t : unitInterval) (g : G) : initial s w hw f y hv (t,Cayley.vertex s g)=y :=
  FixedGraph.homotopy_vertex s (graph s w hw f) y hv t g
def boundaryLoop (g : G) (i : Q) : Path y y := HomotopyTracks.mapped (f:=graph s w hw f) (hv g) (IndexedCells.translated s w hw g i)
def initialTrack (g : G) (i : Q) : Path (boundaryLoop s w hw f y hv g i) (Path.refl y) :=
  HomotopyTracks.track (f:=graph s w hw f) (hv g) (initial s w hw f y hv) (fun t=>initial_vertex s w hw f y hv t g)
    (IndexedCells.translated s w hw g i)
def cellMap (g : G) (i : Q) : C(Disk 2,Y) := f.comp (cell (equivariantFamily (G:=G) (IndexedCells.attaching s w hw)) (g,i))
include hv in
omit [SimplyConnectedSpace Y] in
lemma cellMap_boundary (g : G) (i : Q) (z : Sphere 2) :
    cellMap s w hw f g i (boundary 2 z)=LoopSphere.map (boundaryLoop s w hw f y hv g i) z := by
  change f (cell _ (g,i) (boundary 2 z))=_
  erw [cell_boundary]
  rw [IndexedCells.attaching_translated]
  exact (ContinuousMap.congr_fun (HomotopyTracks.natural_cast (f:=graph s w hw f) (hv g) (IndexedCells.translated s w hw g i)) z).symm
def physical (g : G) (i : Q) : Path (boundaryLoop s w hw f y hv g i) (Path.refl y) :=
  DiskTracks.physical (cellMap s w hw f g i) (cellMap_boundary s w hw f y hv g i)
local instance : CommGroup (FundamentalGroup (Path y y) (Path.refl y)) :=
  { (inferInstance : Group (FundamentalGroup (Path y y) (Path.refl y))) with
    mul_comm:=LoopTracks.loopGroup_comm y }
abbrev Coef := Additive (FundamentalGroup (Path y y) (Path.refl y))
def obstruction (g : G) (i : Q) : Coef y := Additive.ofMul
  (Path.Homotopic.Quotient.mk ((initialTrack s w hw f y hv g i).symm.trans (physical s w hw f y hv g i)))
def obstructionMap : CellModule.Module G Q→+Coef y :=
  Finsupp.liftAddHom (fun e=>zmultiplesHom _ (obstruction s w hw f y hv e.1 e.2))
lemma obstructionMap_single (g : G) (i : Q) : obstructionMap s w hw f y hv (Finsupp.single (g,i) 1)=obstruction s w hw f y hv g i := by
  simp [obstructionMap]
def turnBack : Coef y→+Coef y where
  toFun a := Additive.ofMul ((LoopTranspose.turn y).symm a.toMul)
  map_zero' := (LoopTranspose.turn y).symm.map_one
  map_add' a b := (LoopTranspose.turn y).symm.map_mul a.toMul b.toMul
def correction : CellModule.Module G S→+Coef y := (turnBack y).comp ((obstructionMap s w hw f y hv).comp L)
def labels : C(Cayley.Graph s,Path y y) :=
  GraphLabels.map s (Path.refl y) (fun e=>(correction s w hw L f y hv (Finsupp.single e 1)).toMul)
lemma labels_vertex (g : G) : labels s w hw L f y hv (Cayley.vertex s g)=Path.refl y :=
  GraphLabels.map_vertex _ _ _ g

def final : (graph s w hw f).Homotopy (.const _ y) :=
  (initial s w hw f y hv).trans (HomotopyTracks.run (labels s w hw L f y hv))
lemma final_vertex (t : unitInterval) (g : G) : final s w hw L f y hv (t,Cayley.vertex s g)=y :=
  HomotopyTracks.trans_base (initial s w hw f y hv) (fun t=>initial_vertex s w hw f y hv t g)
    (labels s w hw L f y hv) (labels_vertex s w hw L f y hv g) t

def finalTrack (g : G) (i : Q) : Path (boundaryLoop s w hw f y hv g i) (Path.refl y) :=
  HomotopyTracks.track (f:=graph s w hw f) (hv g) (final s w hw L f y hv) (fun t=>final_vertex s w hw L f y hv t g)
    (IndexedCells.translated s w hw g i)
include hL in
lemma response (g : G) (i : Q) :
    Path.Homotopic.Quotient.mk (LoopTranspose.turnPath y
      (((IndexedCells.translated s w hw g i).map (labels s w hw L f y hv).continuous).cast
        (labels_vertex s w hw L f y hv g).symm (labels_vertex s w hw L f y hv g).symm))=
      (obstruction s w hw f y hv g i).toMul := by
  rw [←LoopTranspose.turn_mk]
  have he := WordResponse.basedClass_equal (IndexedCells.translated_equal s w hw g i)
    (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv g)
    (labels_vertex s w hw L f y hv g)
    (WordResponse.source_eq s (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv) g)
    (WordResponse.target_eq s (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv) g (w i))
  change Path.Homotopic.Quotient.mk (((IndexedCells.translated s w hw g i).map (labels s w hw L f y hv).continuous).cast _ _)=
    (WordResponse.response s (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv) g (w i)).toMul at he
  rw [he]
  have hr:=GraphLabels.realizes s (Path.refl y) (correction s w hw L f y hv) g (w i)
  change WordResponse.response s (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv) g (w i)=_ at hr
  rw [hr]
  change LoopTranspose.turn y ((LoopTranspose.turn y).symm
    ((obstructionMap s w hw f y hv) (L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i))))).toMul)=_
  rw [hL,obstructionMap_single]
  exact (LoopTranspose.turn y).apply_symm_apply _
include hL in
lemma homotopic (g : G) (i : Q) : (physical s w hw f y hv g i).Homotopic (finalTrack s w hw L f y hv g i) := by
  apply Path.Homotopic.Quotient.eq.mp
  change Path.Homotopic.Quotient.mk (physical s w hw f y hv g i)=Path.Homotopic.Quotient.mk
    (HomotopyTracks.track (f:=graph s w hw f) (hv g) ((initial s w hw f y hv).trans (HomotopyTracks.run (labels s w hw L f y hv))) _ _)
  erw [HomotopyTracks.track_trans (f:=graph s w hw f) (hv g) (initial s w hw f y hv)
    (fun t=>initial_vertex s w hw f y hv t g) (labels s w hw L f y hv)
    (labels_vertex s w hw L f y hv g) (IndexedCells.translated s w hw g i)]
  erw [Path.Homotopic.Quotient.mk_trans]
  erw [response s w hw L hL f y hv g i]
  change Path.Homotopic.Quotient.mk (physical s w hw f y hv g i)=
    (Path.Homotopic.Quotient.mk (initialTrack s w hw f y hv g i)).trans
      ((Path.Homotopic.Quotient.mk (initialTrack s w hw f y hv g i)).symm.trans
        (Path.Homotopic.Quotient.mk (physical s w hw f y hv g i)))
  rw [←Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.refl_trans]
end
end TorsionFreeZeroDivisors.AbsorbTracks

end



end OAI
