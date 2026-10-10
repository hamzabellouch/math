import Mathlib
import OAI.Algebra.GroupRing.GraphConeCW
import OAI.Algebra.GroupRing.DiskHomotopy

namespace OAI



section
namespace TorsionFreeZeroDivisors.IndexedCells
open Set Topology GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
noncomputable section
variable {G S Q : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (s : S→G) (w : Q→FreeGroup S) (hw : ∀i,FreeGroup.lift s (w i)=1)
include hw in
omit [TopologicalSpace G] [DiscreteTopology G] in
lemma in_range (r : FreeGroup S) (hr : r∈Set.range w) : FreeGroup.lift s r=1 := by
  rcases hr with ⟨i,rfl⟩;exact hw i
def loop (i : Q) : Path (Cayley.vertex s 1) (Cayley.vertex s 1) :=
  Cayley.relatorLoop s (Set.range w) (in_range s w hw) ⟨w i,⟨i,rfl⟩⟩
lemma loop_equal (i : Q) : PathExtension.Q.Equal (Path.Homotopic.Quotient.mk (loop s w hw i)) (Cayley.wordLift s (w i)).2 :=
  Cayley.relatorLoop_equal s (Set.range w) (in_range s w hw) ⟨w i,⟨i,rfl⟩⟩
def attaching (i : Q) : C(Sphere 2,Cayley.Graph s) := LoopSphere.map (loop s w hw i)
abbrev Cover := CellPresentation.Cover s (attaching s w hw)
abbrev Base := CellPresentation.Base s (attaching s w hw)
def inclusion : C(Cayley.Graph s,Cover s w hw) := CellPresentation.inclusion s (attaching s w hw)
lemma mapped_loop (i : Q) : ((loop s w hw i).map (inclusion s w hw).continuous).Homotopic
    (Path.refl (inclusion s w hw (Cayley.vertex s 1))) := by
  apply LoopSphere.homotopic_map_of_fill _ _ (cell _ ((1:G),i))
  intro z
  change cell (equivariantFamily (G:=G) (attaching s w hw)) ((1:G),i) (boundary 2 z)=_
  erw [cell_boundary]
  simp only [equivariantFamily,ContinuousMap.coe_mk,one_smul]
  rfl
lemma wordLift_rel (i : Q) : CellPresentation.wordLift s (attaching s w hw) (w i)=1 := by
  apply PathExtension.ext (a:=CellPresentation.wordLift s (attaching s w hw) (w i)) (b:=1)
    ((Cayley.wordLift_fst s (w i)).trans (hw i))
  apply PathExtension.Q.Equal.path
  apply (PathExtension.mapFun_equal (inclusion s w hw) (CellPresentation.inclusion_smul s (attaching s w hw))
    (Cayley.vertex s 1) (Cayley.wordLift s (w i))).trans
  apply ((loop_equal s w hw i).map (inclusion s w hw)).symm.trans
  apply (PathExtension.Q.Equal.ofEq (Quotient.sound (mapped_loop s w hw i))).trans
  exact PathExtension.one_path_equal.symm
variable (hs : Function.Surjective (FreeGroup.lift s))
  (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure (Set.range w))
include hs hker in
lemma cover_simplyConnected : SimplyConnectedSpace (Cover s w hw) :=
  CellPresentation.cover_simplyConnected s (attaching s w hw) w (wordLift_rel s w hw) hs hker

def translated (g : G) (i : Q) : Path (Cayley.vertex s g) (Cayley.vertex s g) :=
  ((loop s w hw i).map (smulMap g).continuous).cast
    (by simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,_root_.mul_one])
    (by simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,_root_.mul_one])
lemma translated_equal (g : G) (i : Q) : PathExtension.Q.Equal
    (Path.Homotopic.Quotient.mk (translated s w hw g i)) ((Cayley.wordLift s (w i)).2.map (smulMap g)) :=
  (PathExtension.Q.cast_equal _ _ _).trans ((loop_equal s w hw i).map _)
lemma attaching_translated (g : G) (i : Q) (z : Sphere 2) :
    equivariantFamily (G:=G) (attaching s w hw) (g,i) z=LoopSphere.map (translated s w hw g i) z := by
  exact (ContinuousMap.congr_fun (HomotopyTracks.natural_cast
    (f:=smulMap g) (by simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,_root_.mul_one])
    (loop s w hw i)) z).symm
end
end TorsionFreeZeroDivisors.IndexedCells

end



end OAI
