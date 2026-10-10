import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FramedFlags

namespace OAI

/-!
# Transport of local frames along seams

The column and parent coordinate identifications transport local frame matrices
between the two ends of a surface seam.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity)
lemma portParentMatch_index (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.portParentMatch p u h).trans (D.portRowIndex u)=
      (D.portRowIndex p).trans (finCongr (congrArg D.seamDim h)) := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rfl
lemma localFrameUnit_match (f : D.PortFrames (R:=R)) (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (hs : (f u).reindex (D.portColumnMatch p u h) (D.portParentMatch p u h)=f p) :
    (MatrixIso.unit (D.localFrameUnit f u)).reindex
      (finCongr (congrArg D.seamDim h)) (finCongr (congrArg D.seamDim h))=
      MatrixIso.unit (D.localFrameUnit f p) := by
  have hh := congrArg (fun z => z.reindex (D.portColumnIndex p).symm (D.portRowIndex p).symm) hs
  simp only [MatrixIso.reindex_reindex_eq,D.portColumnMatch_from_index,D.portParentMatch_from_index] at hh
  simpa only [localFrameUnit,MatrixIso.unit_toUnit,MatrixIso.reindex_reindex_eq] using hh
lemma localFrameUnit_rebase_match (f : D.PortFrames (R:=R)) (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (hs : (f u).reindex (D.portColumnMatch p u h) (D.portParentMatch p u h)=f p) :
    rebaseUnit (congrArg D.seamDim h).symm (D.localFrameUnit f u)=D.localFrameUnit f p := by
  have hh := D.localFrameUnit_match f p u h hs
  have he : finCongr (congrArg D.seamDim h)=finCongr (congrArg D.seamDim h).symm.symm := rfl
  rw [he,←rebaseUnit_iso] at hh
  exact congrArg MatrixIso.toUnit hh
lemma frameValues_match (f : D.PortFrames (R:=R)) (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (hs : (f u).reindex (D.portColumnMatch p u h) (D.portParentMatch p u h)=f p) :
    rebaseUnit (congrArg D.seamDim h).symm
      (D.frameValues f (D.ports.attach u).1 (D.ports.attach u).2)=
      D.frameValues f (D.ports.attach p).1 (D.ports.attach p).2 := by
  rw [D.frameValues_attach,D.frameValues_attach]
  exact D.localFrameUnit_rebase_match f p u h hs
lemma frameValues_seam_of_ports (f : D.PortFrames (R:=R))
    (p u : LocalPort V D.ports.kind) (s : S)
    (hp : D.ports.attach p=(s,false)) (hu : D.ports.attach u=(s,true))
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (hs : (f u).reindex (D.portColumnMatch p u h) (D.portParentMatch p u h)=f p) :
    D.frameValues f s false=D.frameValues f s true := by
  have hh := D.frameValues_match f p u h hs
  have aux {a b : S × Bool} (ha : a=(s,false)) (hb : b=(s,true))
      (he : a.1=b.1)
      (ht : rebaseUnit (congrArg D.seamDim he).symm
        (D.frameValues f b.1 b.2)=D.frameValues f a.1 a.2) :
      D.frameValues f s false=D.frameValues f s true := by
    subst a
    subst b
    simpa only [rebaseUnit_refl] using ht.symm
  exact aux hp hu h hh
lemma attachedEnds_same (s : S) :
    (D.ports.attach (D.ports.attach.symm (s,false))).1=
      (D.ports.attach (D.ports.attach.symm (s,true))).1 := by
  simp only [Equiv.apply_symm_apply]
lemma frameValues_seam_match (f : D.PortFrames (R:=R)) (s : S)
    (hs : (f (D.ports.attach.symm (s,true))).reindex
      (D.portColumnMatch (D.ports.attach.symm (s,false)) (D.ports.attach.symm (s,true))
        (D.attachedEnds_same s))
      (D.portParentMatch (D.ports.attach.symm (s,false)) (D.ports.attach.symm (s,true))
        (D.attachedEnds_same s))=f (D.ports.attach.symm (s,false))) :
    D.frameValues f s false=D.frameValues f s true := by
  have hh := D.frameValues_match f (D.ports.attach.symm (s,false))
    (D.ports.attach.symm (s,true)) (D.attachedEnds_same s) hs
  have aux {a b : S × Bool} (ha : a=(s,false)) (hb : b=(s,true))
      (he : a.1=b.1)
      (ht : rebaseUnit (congrArg D.seamDim he).symm
        (D.frameValues f b.1 b.2)=D.frameValues f a.1 a.2) :
      D.frameValues f s false=D.frameValues f s true := by
    subst a
    subst b
    simpa only [rebaseUnit_refl] using ht.symm
  exact aux (D.ports.attach.apply_symm_apply (s,false))
    (D.ports.attach.apply_symm_apply (s,true)) (D.attachedEnds_same s) hh
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
