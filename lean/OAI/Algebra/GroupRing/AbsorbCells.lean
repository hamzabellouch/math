import Mathlib
import OAI.Algebra.GroupRing.AbsorbTracks

namespace OAI



section
namespace TorsionFreeZeroDivisors.AbsorbCells
open Set GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
noncomputable section
variable {G S Q Y : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] [SimplyConnectedSpace Y]
  (s : S→G) (w : Q→FreeGroup S) (hw : ∀i,FreeGroup.lift s (w i)=1)
  (L : CellModule.Module G S→+CellModule.Module G Q)
  (hL : ∀g i,L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i)))=Finsupp.single (g,i) 1)
  (f : C(IndexedCells.Cover s w hw,Y)) (y : Y)
  (hv : ∀g,f (IndexedCells.inclusion s w hw (Cayley.vertex s g))=y)
def graphHomotopy : (AbsorbTracks.graph s w hw f).Homotopy (.const _ y) :=
  (ContinuousMap.Homotopy.refl _).trans (AbsorbTracks.final s w hw L f y hv)
def diskHomotopy (e : G×Q) : (AbsorbTracks.cellMap s w hw f e.1 e.2).Homotopy (.const _ y) :=
  DiskTracks.extension (AbsorbTracks.cellMap s w hw f e.1 e.2)
    (AbsorbTracks.cellMap_boundary s w hw f y hv e.1 e.2)
    (AbsorbTracks.finalTrack s w hw L f y hv e.1 e.2)
    (AbsorbTracks.homotopic s w hw L hL f y hv e.1 e.2).some
lemma diskHomotopy_boundary (e : G×Q) (t : unitInterval) (z : Sphere 2) :
    diskHomotopy s w hw L hL f y hv e (t,boundary 2 z)=
      graphHomotopy s w hw L f y hv (t,equivariantFamily (G:=G) (IndexedCells.attaching s w hw) e z) := by
  change DiskTracks.extension _ _ _ _ (t,boundary 2 z)=_
  erw [DiskTracks.extension_boundary]
  change _=((ContinuousMap.Homotopy.refl _).trans (AbsorbTracks.final s w hw L f y hv)) _
  rw [ContinuousMap.Homotopy.trans_apply,IndexedCells.attaching_translated]
  split_ifs
  · exact ContinuousMap.congr_fun (HomotopyTracks.natural_cast (f:=AbsorbTracks.graph s w hw f) (hv e.1) (IndexedCells.translated s w hw e.1 e.2)) z
  · exact HomotopyTracks.track_boundary (f:=AbsorbTracks.graph s w hw f) (hv e.1) (AbsorbTracks.final s w hw L f y hv)
      (fun t=>AbsorbTracks.final_vertex s w hw L f y hv t e.1) (IndexedCells.translated s w hw e.1 e.2) _ z

def graphPaths : C(Cayley.Graph s,C(unitInterval,Y)) :=
  ((graphHomotopy s w hw L f y hv).toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
def cellPaths (e : G×Q) : C(Disk 2,C(unitInterval,Y)) :=
  ((diskHomotopy s w hw L hL f y hv e).toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
lemma paths_boundary (e : G×Q) (z : Sphere 2) : cellPaths s w hw L hL f y hv e (boundary 2 z)=
    graphPaths s w hw L f y hv (equivariantFamily (G:=G) (IndexedCells.attaching s w hw) e z) := by
  ext t
  exact diskHomotopy_boundary s w hw L hL f y hv e t z
def paths : C(IndexedCells.Cover s w hw,C(unitInterval,Y)) :=
  lift (equivariantFamily (G:=G) (IndexedCells.attaching s w hw))
    (graphPaths s w hw L f y hv) (cellPaths s w hw L hL f y hv) (paths_boundary s w hw L hL f y hv)
lemma paths_zero (z : IndexedCells.Cover s w hw) : paths s w hw L hL f y hv z 0=f z := by
  cases z with
  | inl z => exact (graphHomotopy s w hw L f y hv).apply_zero z
  | inr z =>
    change diskHomotopy s w hw L hL f y hv z.1 (0,interior 2 z.2)=_
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (cell _ z.1 (interior 2 z.2))=f (Sum.inr z)
    rw [cell_interior]
lemma paths_one (z : IndexedCells.Cover s w hw) : paths s w hw L hL f y hv z 1=y := by
  cases z with
  | inl z=>exact (graphHomotopy s w hw L f y hv).apply_one z
  | inr z=>exact (diskHomotopy s w hw L hL f y hv z.1).apply_one (interior 2 z.2)
def homotopy : f.Homotopy (.const _ y) where
  toFun z:=paths s w hw L hL f y hv z.2 z.1
  continuous_toFun:=(paths s w hw L hL f y hv).uncurry.continuous.comp continuous_swap
  map_zero_left:=paths_zero s w hw L hL f y hv
  map_one_left:=paths_one s w hw L hL f y hv
end
end TorsionFreeZeroDivisors.AbsorbCells

end



end OAI
