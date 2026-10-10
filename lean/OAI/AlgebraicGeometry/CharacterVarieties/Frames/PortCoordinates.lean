import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.LocalFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FramedFlags

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)

lemma portNamedFrame (f : D.PortFrames (R:=K)) (p : LocalPort V D.ports.kind) :
    D.namedSeamFrame (D.ports.attach p).1 (D.frameValues f (D.ports.attach p).1 (D.ports.attach p).2)=
      ((f p).reindex (D.portNamedColumns p) (Equiv.refl _)).linearEquiv := by
  erw [D.frameValues_attach]
  unfold namedSeamFrame localFrameUnit
  erw [MatrixIso.unit_toUnit,MatrixIso.reindex_reindex_eq]
  have hr : (finCongr (D.seamRank (D.ports.attach p).1)).trans (D.portRowIndex p).symm=Equiv.refl _ :=
    Equiv.self_trans_symm _
  have hc : (blockIndex (D.childDim (D.ports.attach p).1)).symm.trans
      (D.portColumnIndex p).symm=D.portNamedColumns p := by
    unfold portColumnIndex portNamedColumns
    apply Equiv.ext
    intro i
    erw [Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.symm_symm_apply,Equiv.apply_symm_apply]
    rfl
  erw [hr,hc]
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end



noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades VertexTable
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "W" => BandGraft.wiring (A) q (B)

/-- A port of the cut diagram is attached to a specified seam end. -/
def CutPortAttached (p : LocalPort _ (BandGraft.kind (A) q (B)))
    (e : (W).Seam × Bool) : Prop :=
  (C).ports.attach p=e

/-- Two ports of the cut diagram meet the same seam. -/
def CutPortsAdjacent (p u : LocalPort _ (BandGraft.kind (A) q (B))) : Prop :=
  ((C).ports.attach p).1=((C).ports.attach u).1
lemma origInput_attach (v : Fin (w.shape.atomicBand.length+1)) :
    D.CutPortAttached q w ⟨.inr (.inl v),(w.shape.atomicBand.kind v).input⟩
      (BandGraft.originalPort (A) q (B) v true,true) := by
  change (C).ports.attach ⟨.inr (.inl v),(w.shape.atomicBand.kind v).input⟩=_
  exact (W).endOf_portAt (BandGraft.originalPort (A) q (B) v true,true)
lemma origOutput_attach (j : Fin w.shape.atomicBand.length) :
    D.CutPortAttached q w
      ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
      (BandGraft.originalPort (A) q (B) j.succ true,false) := by
  change (C).ports.attach
    ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩=_
  have hh := (W).endOf_portAt (BandGraft.originalPort (A) q (B) j.succ true,false)
  change (W).endOf ((W).wire (BandGraft.originalPort (A) q (B) j.succ true)).val=_ at hh
  erw [BandGraft.wire_original] at hh
  exact hh
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)
lemma mirror_vertex_frame_seam (T : MatrixIso K (Fin r) (Fin r))
    (v u : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).mirror.table.Port)
    (q : (w.shape.atomicBand.kind u).mirror.table.Port)
    (c : (w.shape.atomicBand.kind v).mirror.table.Child p ≃
      (w.shape.atomicBand.kind u).mirror.table.Child q)
    (hp : ((w.shape.atomicBand.decoration v).mirror).color ⟨p,none⟩=
      ((w.shape.atomicBand.decoration u).mirror).color ⟨q,none⟩)
    (hc : ∀ a,((w.shape.atomicBand.decoration v).mirror).color ⟨p,some a⟩=
      ((w.shape.atomicBand.decoration u).mirror).color ⟨q,some (c a)⟩) :
    (w.mirrorVertexFrames T u q).reindex
      ((w.shape.vertexAtoms v).mirror.seamColumns (w.shape.vertexAtoms u).mirror p q c
        (fun a => congrArg w.shape.facetAtoms (hc a)))
      (finCongr ((w.shape.vertexAtoms v).mirror.rank_of_atoms (w.shape.vertexAtoms u).mirror
        (congrArg w.shape.facetAtoms hp)))=w.mirrorVertexFrames T v p := by
  apply (w.shape.vertexAtoms v).mirror.reframe_seam (w.shape.vertexAtoms u).mirror
    (w.mirrorVertexBases T v) (w.mirrorVertexBases T u) p q c
    (congrArg w.shape.facetAtoms hp) (fun a => congrArg w.shape.facetAtoms (hc a))
  · exact MatrixIso.finite_basis_transport _ (w.mirrorColorGauge T) _ _ _ _ _ _ hp _
  · intro a
    exact MatrixIso.finite_basis_transport _ (w.mirrorColorGauge T) _ _ _ _ _ _ (hc a) _

def mirrorInteriorChild (j : Fin w.shape.atomicBand.length) :
    (w.shape.atomicBand.kind j.castSucc).mirror.table.Child
      ((w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output) ≃
    (w.shape.atomicBand.kind j.succ).mirror.table.Child
      ((w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input) :=
  ((w.shape.atomicBand.kind j.castSucc).mirrorChild _).symm.trans
    ((w.interiorChild j).trans ((w.shape.atomicBand.kind j.succ).mirrorChild _))

lemma mirror_interior_parent (j : Fin w.shape.atomicBand.length) :
    ((w.shape.atomicBand.decoration j.castSucc).mirror).color
      ⟨(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output,none⟩=
    ((w.shape.atomicBand.decoration j.succ).mirror).color
      ⟨(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input,none⟩ := by
  exact ((w.shape.atomicBand.decoration j.castSucc).mirror_color
    ⟨(w.shape.atomicBand.kind j.castSucc).output,none⟩).trans
      ((w.interior_parent j).trans
        ((w.shape.atomicBand.decoration j.succ).mirror_color
          ⟨(w.shape.atomicBand.kind j.succ).input,none⟩).symm)

lemma mirror_interior_child (j : Fin w.shape.atomicBand.length) (a) :
    ((w.shape.atomicBand.decoration j.castSucc).mirror).color
      ⟨(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output,some a⟩=
    ((w.shape.atomicBand.decoration j.succ).mirror).color
      ⟨(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input,
        some (w.mirrorInteriorChild j a)⟩ := by
  obtain ⟨a,rfl⟩ := ((w.shape.atomicBand.kind j.castSucc).mirrorChild _).surjective a
  have he : w.mirrorInteriorChild j ((w.shape.atomicBand.kind j.castSucc).mirrorChild _ a)=
      (w.shape.atomicBand.kind j.succ).mirrorChild _ (w.interiorChild j a) := by
    simp only [mirrorInteriorChild,Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [he]
  exact ((w.shape.atomicBand.decoration j.castSucc).mirror_color
    ⟨(w.shape.atomicBand.kind j.castSucc).output,some a⟩).trans
      ((w.interior_child j a).trans
        ((w.shape.atomicBand.decoration j.succ).mirror_color
          ⟨(w.shape.atomicBand.kind j.succ).input,some (w.interiorChild j a)⟩).symm)

lemma mirror_interior_frame_seam (T : MatrixIso K (Fin r) (Fin r))
    (j : Fin w.shape.atomicBand.length) :
    (w.mirrorVertexFrames T j.succ
      ((w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input)).reindex
      ((w.shape.vertexAtoms j.castSucc).mirror.seamColumns (w.shape.vertexAtoms j.succ).mirror
        _ _ (w.mirrorInteriorChild j)
        (fun a => congrArg w.shape.facetAtoms (w.mirror_interior_child j a)))
      (finCongr ((w.shape.vertexAtoms j.castSucc).mirror.rank_of_atoms (w.shape.vertexAtoms j.succ).mirror
        (congrArg w.shape.facetAtoms (w.mirror_interior_parent j))))=
      w.mirrorVertexFrames T j.castSucc
        ((w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output) :=
  w.mirror_vertex_frame_seam T _ _ _ _ _ (w.mirror_interior_parent j) (w.mirror_interior_child j)
end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades VertexTable
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "W" => BandGraft.wiring (A) q (B)
lemma firstOldNegative_attach :
    D.CutPortAttached q w
      ⟨.inl (D.ports.attach.symm (q,false)).1,(D.ports.attach.symm (q,false)).2⟩
      (BandGraft.originalPort (A) q (B) 0 true,false) := by
  change (C).ports.attach
    ⟨.inl (D.ports.attach.symm (q,false)).1,(D.ports.attach.symm (q,false)).2⟩=_
  have hh := (W).endOf_portAt (BandGraft.originalPort (A) q (B) 0 true,false)
  change (W).endOf ((W).wire (BandGraft.originalPort (A) q (B) 0 true)).val=_ at hh
  erw [BandGraft.wire_first] at hh
  exact hh
lemma lastOriginalOutput_attach :
    D.CutPortAttached q w
      ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),
        (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output⟩
      (BandGraft.oldPort (A) q (B) q true,false) := by
  change (C).ports.attach
    ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),
      (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output⟩=_
  have hh := (W).endOf_portAt (BandGraft.oldPort (A) q (B) q true,false)
  change (W).endOf ((W).wire (BandGraft.oldPort (A) q (B) q true)).val=_ at hh
  erw [BandGraft.wire_last] at hh
  exact hh
lemma lastOldPositive_attach :
    D.CutPortAttached q w
      ⟨.inl (D.ports.attach.symm (q,true)).1,(D.ports.attach.symm (q,true)).2⟩
      (BandGraft.oldPort (A) q (B) q true,true) := by
  change (C).ports.attach
    ⟨.inl (D.ports.attach.symm (q,true)).1,(D.ports.attach.symm (q,true)).2⟩=_
  exact (W).endOf_portAt (BandGraft.oldPort (A) q (B) q true,true)
lemma mirrorFirstInput_attach :
    D.CutPortAttached q w
      ⟨.inr (.inr 0),(w.shape.atomicBand.kind 0).mirrorPort
        (w.shape.atomicBand.kind 0).input⟩
      (BandGraft.mirrorOutput (A) q (B) (Fin.last w.shape.atomicBand.length),false) := by
  change (C).ports.attach
    ⟨.inr (.inr 0),(w.shape.atomicBand.kind 0).mirrorPort
      (w.shape.atomicBand.kind 0).input⟩=_
  have hh := (W).endOf_portAt
    (BandGraft.mirrorOutput (A) q (B) (Fin.last w.shape.atomicBand.length),false)
  change (W).endOf ((W).wire
    (BandGraft.mirrorOutput (A) q (B) (Fin.last w.shape.atomicBand.length))).val=_ at hh
  have hw : (W).wire (BandGraft.mirrorOutput (A) q (B) (Fin.last w.shape.atomicBand.length))=
      BandGraft.mirrorInput (A) q (B) 0 := BandGraft.wire_mirror_wrap (A) q (B)
  rw [hw] at hh
  exact hh
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type} [CommRing R] {k l : Kind} {d d' : LocalRanks k} {e e' : LocalRanks l}
lemma transportFrames_seam (hd : d=d') (he : e=e')
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p))
    (g : (p : l.table.Port) → MatrixIso R (e.Columns p) (e.Parent p))
    (p : k.table.Port) (q : l.table.Port)
    (c : d.Columns p ≃ e.Columns q) (r : d.Parent p ≃ e.Parent q)
    (hs : (g q).reindex c r=f p) :
    (transportFrames he g q).reindex
      (((columnCongr hd p).symm.trans c).trans (columnCongr he q))
      (((parentCongr hd p).symm.trans r).trans (parentCongr he q))=
      transportFrames hd f p := by
  subst d'
  subst e'
  have hc (a : LocalRanks k) (p : k.table.Port) : columnCongr (d:=a) rfl p=Equiv.refl _ := Equiv.ext (fun _ => rfl)
  have hr (a : LocalRanks k) (p : k.table.Port) : parentCongr (d:=a) rfl p=Equiv.refl _ := by ext i; rfl
  have hc' (a : LocalRanks l) (p : l.table.Port) : columnCongr (d:=a) rfl p=Equiv.refl _ := Equiv.ext (fun _ => rfl)
  have hr' (a : LocalRanks l) (p : l.table.Port) : parentCongr (d:=a) rfl p=Equiv.refl _ := by ext i; rfl
  rw [hc,hr,hc',hr']
  change (g q).reindex (((Equiv.refl _).trans c).trans (Equiv.refl _))
    (((Equiv.refl _).trans r).trans (Equiv.refl _))=f p
  simpa only [Equiv.refl_trans,Equiv.trans_refl] using hs
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
omit [Finite V] in
lemma portChildMatch_enumeration (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) (c) :
    (((D.ports.kind u.1).childEnumeration u.2) (D.portChildMatch p u h c)).val=
      (((D.ports.kind p.1).childEnumeration p.2) c).val := by
  unfold portChildMatch PortAssembly.childEquiv
  simp only [Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl
lemma origAdjacentSame (j : Fin w.shape.atomicBand.length) :
    D.CutPortsAdjacent q w
      ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
      ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩ := by
  change ((C).ports.attach
    ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩).1=_
  exact (congrArg Prod.fst (D.origOutput_attach q w j)).trans
    (congrArg Prod.fst (D.origInput_attach q w j.succ)).symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V : Type} {arity : S → ℕ}
    (D : Diagram F S V arity)
lemma portChildMatch_eq_of_enumeration (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (e : (D.ports.kind p.1).table.Child p.2 ≃ (D.ports.kind u.1).table.Child u.2)
    (he : ∀ c, (((D.ports.kind u.1).childEnumeration u.2) (e c)).val=
      (((D.ports.kind p.1).childEnumeration p.2) c).val) :
    D.portChildMatch p u h=e := by
  apply Equiv.ext
  intro c
  apply ((D.ports.kind u.1).childEnumeration u.2).injective
  apply Fin.ext
  exact (D.portChildMatch_enumeration p u h c).trans (he c).symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "oo" => D.ports.attach.symm (q,false)
lemma firstAdjacentSame :
    D.CutPortsAdjacent q w ⟨.inl (oo).1,(oo).2⟩
      ⟨.inr (.inl 0),(w.shape.atomicBand.kind 0).input⟩ := by
  change ((C).ports.attach ⟨.inl (oo).1,(oo).2⟩).1=_
  exact (congrArg Prod.fst (D.firstOldNegative_attach q w)).trans
    (congrArg Prod.fst (D.origInput_attach q w 0)).symm

def cutFirstChild : (D.ports.kind (oo).1).table.Child (oo).2 ≃
    (w.shape.atomicBand.kind 0).table.Child (w.shape.atomicBand.kind 0).input :=
  ((D.ports.childEquiv (oo)).trans
    (finCongr (congrArg arity (congrArg Prod.fst (D.ports.attach.apply_symm_apply (q,false)))))).trans
      w.firstChild.symm

omit [Finite V] in
lemma cutFirstChild_enumeration (c : (D.ports.kind (oo).1).table.Child (oo).2) :
    (((w.shape.atomicBand.kind 0).childEnumeration (w.shape.atomicBand.kind 0).input)
      (D.cutFirstChild q w c)).val=
      (((D.ports.kind (oo).1).childEnumeration (oo).2) c).val := by
  unfold cutFirstChild IdentifiedBand.firstChild PortAssembly.childEquiv
  simp only [Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

/-- Child transport from the old negative end to the first vertex of the cut band. -/
def firstCutChildTransport :
    (D.ports.kind (oo).1).table.Child (oo).2 ≃
      (w.shape.atomicBand.kind 0).table.Child (w.shape.atomicBand.kind 0).input :=
  (C).portChildMatch ⟨.inl (oo).1,(oo).2⟩
    ⟨.inr (.inl 0),(w.shape.atomicBand.kind 0).input⟩ (D.firstAdjacentSame q w)

lemma firstChildMatch :
    D.firstCutChildTransport q w=D.cutFirstChild q w := by
  change (C).portChildMatch ⟨.inl (oo).1,(oo).2⟩
    ⟨.inr (.inl 0),(w.shape.atomicBand.kind 0).input⟩
    (D.firstAdjacentSame q w)=D.cutFirstChild q w
  apply (C).portChildMatch_eq_of_enumeration
  exact D.cutFirstChild_enumeration q w
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {k l : Kind} {d d' : LocalRanks k} {e e' : LocalRanks l}
lemma columnCongr_sandwich (hd : d=d') (he : e=e')
    (p : k.table.Port) (q : l.table.Port)
    (c c' : k.table.Child p ≃ l.table.Child q) (hcc : c=c')
    (hc : ∀ a,d.rank p (some a)=e.rank q (some (c a)))
    (hc' : ∀ a,d'.rank p (some a)=e'.rank q (some (c' a))) :
    (((columnCongr hd p).symm.trans (Equiv.sigmaCongr c (fun a=>finCongr (hc a)))).trans
      (columnCongr he q))=Equiv.sigmaCongr c' (fun a=>finCongr (hc' a)) := by
  subst d'
  subst e'
  subst c'
  apply Equiv.ext
  intro i
  apply Sigma.ext
  · rfl
  · rfl
lemma parentCongr_sandwich (hd : d=d') (he : e=e')
    (p : k.table.Port) (q : l.table.Port)
    (h : d.rank p none=e.rank q none) (h' : d'.rank p none=e'.rank q none) :
    (((parentCongr hd p).symm.trans (finCongr h)).trans
      (parentCongr he q))=finCongr h' := by
  ext i
  rfl
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity)
lemma transported_portFrame_match (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    {d : LocalRanks (D.ports.kind p.1)} {e : LocalRanks (D.ports.kind u.1)}
    (hd : d=D.vertexRanks p.1) (he : e=D.vertexRanks u.1)
    (f : (v : (D.ports.kind p.1).table.Port) → MatrixIso R (d.Columns v) (d.Parent v))
    (g : (v : (D.ports.kind u.1).table.Port) → MatrixIso R (e.Columns v) (e.Parent v))
    (c : (D.ports.kind p.1).table.Child p.2 ≃ (D.ports.kind u.1).table.Child u.2)
    (hcc : c=D.portChildMatch p u h)
    (hc : ∀ a,d.rank p.2 (some a)=e.rank u.2 (some (c a)))
    (hr : d.rank p.2 none=e.rank u.2 none)
    (hs : (g u.2).reindex (Equiv.sigmaCongr c (fun a=>finCongr (hc a))) (finCongr hr)=f p.2) :
    (LocalRanks.transportFrames he g u.2).reindex
      (D.portColumnMatch p u h) (D.portParentMatch p u h)=
      LocalRanks.transportFrames hd f p.2 := by
  have hh := LocalRanks.transportFrames_seam hd he f g p.2 u.2
    (Equiv.sigmaCongr c (fun a=>finCongr (hc a))) (finCongr hr) hs
  rw [LocalRanks.columnCongr_sandwich hd he p.2 u.2 c (D.portChildMatch p u h)
    hcc hc (D.portChildRank_match p u h),
    LocalRanks.parentCongr_sandwich hd he p.2 u.2 hr (D.portParentRank_match p u h)] at hh
  exact hh
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)
lemma seamGrade_portColumnIndex (p : LocalPort V D.ports.kind)
    (i : (D.vertexRanks p.1).Columns p.2) :
    D.seamGrade (D.ports.attach p).1 (D.portColumnIndex p i)=
      ((D.ports.kind p.1).childEnumeration p.2 i.1).val := by
  change ((blockIndex (D.childDim (D.ports.attach p).1))
    ((blockIndex (D.childDim (D.ports.attach p).1)).symm
      ⟨D.ports.childEquiv p i.1,i.2⟩)).1.val=_
  rw [Equiv.apply_symm_apply]
  rfl
lemma portFrame_namedCoordinates
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool)
    (ha : D.ports.attach p=(s,b)) :
    ((D.portFrame g p).reindex
      ((D.namedColumnsMatch (congrArg Prod.fst ha)).symm.trans (D.portNamedColumns p))
      (finCongr (congrArg (fun z=>D.rank (D.ports.facet ⟨z,none⟩))
        (congrArg Prod.fst ha)).symm)).linearEquiv=
      D.namedSeamFrame s (g (.frame s b)) := by
  have h1 : (D.ports.attach p).1=s := congrArg Prod.fst ha
  have h2 : (D.ports.attach p).2=b := congrArg Prod.snd ha
  subst s
  subst b
  rw [D.namedColumnsMatch_refl]
  simp only [Equiv.refl_symm,Equiv.refl_trans]
  unfold portFrame namedSeamFrame
  erw [MatrixIso.reindex_reindex_eq]
  have hc : (D.portNamedColumns p).trans (D.portColumnIndex p)=
      (blockIndex (D.childDim (D.ports.attach p).1)).symm := by
    unfold portNamedColumns portColumnIndex
    erw [←Equiv.trans_assoc,Equiv.symm_trans_self,Equiv.refl_trans]
  erw [hc,Equiv.refl_trans]
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
