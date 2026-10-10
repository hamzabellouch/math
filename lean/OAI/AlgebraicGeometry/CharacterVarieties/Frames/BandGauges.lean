import OAI.AlgebraicGeometry.CharacterVarieties.Frames.BandBases

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
namespace IdentifiedBand
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

def fiberEnum (c : Option (Secondary n n)) :
    {a : w.shape.Atom // a∈w.shape.facetAtoms c} ≃ Fin (freshRank r w.shape.secondaryRank c) :=
  (Fintype.equivFin _).trans (finCongr (w.shape.card_facetAtoms c))

def rowFiberEquiv (i : Fin n) :
    {a : w.shape.Atom // a∈w.shape.facetAtoms (some (.row i))} ≃
      {a // rowGrade w.shape a=i.val} :=
  Equiv.subtypeEquivRight fun _ => Fin.ext_iff

def colFiberEquiv (i : Fin n) :
    {a : w.shape.Atom // a∈w.shape.facetAtoms (some (.col i))} ≃
      {a // colGrade w.shape a=i.val} :=
  Equiv.subtypeEquivRight fun _ => Fin.ext_iff

def parentGauge : (Fin r → K) ≃ₗ[K] (Fin r → K) :=
  (LinearEquiv.funCongrLeft K K (w.fiberEnum none)).trans
    ((LinearEquiv.funCongrLeft K K (Equiv.Set.univ w.shape.Atom).symm).trans w.frame)

def rowGauge (i : Fin n) :
    (Fin (w.shape.secondaryRank (.row i)) → K) ≃ₗ[K]
      (Fin (w.shape.secondaryRank (.row i)) → K) :=
  (LinearEquiv.funCongrLeft K K (w.fiberEnum (some (.row i)))).trans
    ((LinearEquiv.funCongrLeft K K (w.rowFiberEquiv i).symm).trans
      ((w.row i.val).trans
        ((LinearEquiv.funCongrLeft K K (sigmaGradeEquiv s i).symm).trans
          (LinearEquiv.funCongrLeft K K (finCongr (w.rowRanks i)).symm))))

def colGauge (i : Fin n) :
    (Fin (w.shape.secondaryRank (.col i)) → K) ≃ₗ[K]
      (Fin (w.shape.secondaryRank (.col i)) → K) :=
  (LinearEquiv.funCongrLeft K K (w.fiberEnum (some (.col i)))).trans
    ((LinearEquiv.funCongrLeft K K (w.colFiberEquiv i).symm).trans
      ((w.col i.val).trans
        ((LinearEquiv.funCongrLeft K K (sigmaGradeEquiv s i).symm).trans
          (LinearEquiv.funCongrLeft K K (finCongr (w.colRanks i)).symm))))

/-- Row and column contacts have separate named gauges, including when their facet labels coincide. -/
def colorGauge (c : Option (Secondary n n)) :
    MatrixIso K (Fin (freshRank r w.shape.secondaryRank c))
      (Fin (freshRank r w.shape.secondaryRank c)) := by
  rcases c with _|(_|_|_)
  · exact MatrixIso.ofLinearEquiv w.parentGauge
  · exact MatrixIso.ofLinearEquiv (w.rowGauge _)
  · exact MatrixIso.ofLinearEquiv (w.colGauge _)
  · exact MatrixIso.refl

def vertexBases (v : Fin (w.shape.atomicBand.length+1)) :
    (w.shape.vertexAtoms v).localRanks.CoherentBases (R:=K) :=
  LocalRanks.colorBases _ (w.shape.atomicBand.decoration v)
    (freshRank r w.shape.secondaryRank) (fun p c => w.shape.vertexAtoms_rank v ⟨p,c⟩) w.colorGauge

def vertexFrames (v : Fin (w.shape.atomicBand.length+1)) :
    (p : (w.shape.atomicBand.kind v).table.Port) →
      MatrixIso K ((w.shape.vertexAtoms v).localRanks.Columns p)
        ((w.shape.vertexAtoms v).localRanks.Parent p) :=
  (w.vertexBases v).reframe (w.shape.vertexAtoms v).frame

lemma vertexFrames_holds (v : Fin (w.shape.atomicBand.length+1)) :
    (LocalRanks.comparison _ _ (w.vertexFrames v)).Holds :=
  (w.vertexBases v).comparison_holds _ (w.shape.vertexAtoms v).comparison_holds

/-- The mirror gauge changes only the principal rank fiber; lower strip fibers retain their named
gauges. -/
def mirrorColorGauge (T : MatrixIso K (Fin r) (Fin r)) (c : Option (Secondary n n)) :
    MatrixIso K (Fin (freshRank r w.shape.secondaryRank c))
      (Fin (freshRank r w.shape.secondaryRank c)) := by
  cases c with
  | none => exact (w.colorGauge none).trans T.symm
  | some c => exact w.colorGauge (some c)

def mirrorVertexBases (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) :
    (w.shape.vertexAtoms v).mirror.localRanks.CoherentBases (R:=K) :=
  LocalRanks.colorBases _ (w.shape.atomicBand.decoration v).mirror
    (freshRank r w.shape.secondaryRank)
    (fun p c => w.shape.vertexAtoms_rank v ((w.shape.atomicBand.kind v).mirrorEnd.symm ⟨p,c⟩))
    (w.mirrorColorGauge T)

def mirrorVertexFrames (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) :
    (p : (w.shape.atomicBand.kind v).mirror.table.Port) →
      MatrixIso K ((w.shape.vertexAtoms v).mirror.localRanks.Columns p)
        ((w.shape.vertexAtoms v).mirror.localRanks.Parent p) :=
  (w.mirrorVertexBases T v).reframe (w.shape.vertexAtoms v).mirror.frame

lemma mirrorVertexFrames_holds (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) :
    (LocalRanks.comparison _ _ (w.mirrorVertexFrames T v)).Holds :=
  (w.mirrorVertexBases T v).comparison_holds _ (w.shape.vertexAtoms v).mirror.comparison_holds

end IdentifiedBand
end IntegralCharacterVarieties.NamedBandGrades
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
open scoped Classical
variable {A : Type} [Fintype A] {k l : Kind} (D : AtomicData k A) (E : AtomicData l A)

lemma rank_of_atoms {z w} (h : D.atoms z=E.atoms w) : D.rank z=E.rank w :=
  congrArg (fun s : Set A => Fintype.card {a // a∈s}) h

lemma atom_cast_other {z w} (h : D.atoms z=E.atoms w) (hr : D.rank z=E.rank w)
    (i : Fin (D.rank z)) : E.atom w (finCongr hr i)=D.atom z i := by
  have aux (s t : Set A) (h : s=t)
      (hr : Fintype.card {a // a∈s}=Fintype.card {a // a∈t})
      (i : Fin (Fintype.card {a // a∈s})) :
      ((Fintype.equivFin {a // a∈t}).symm (finCongr hr i)).val=
        ((Fintype.equivFin {a // a∈s}).symm i).val := by
    subst t
    rfl
  exact aux _ _ h hr i

def seamColumns (p : k.table.Port) (q : l.table.Port)
    (c : k.table.Child p ≃ l.table.Child q)
    (hc : ∀ a,D.atoms ⟨p,some a⟩=E.atoms ⟨q,some (c a)⟩) :
    D.localRanks.Columns p ≃ E.localRanks.Columns q :=
  Equiv.sigmaCongr c (fun a => finCongr (D.rank_of_atoms E (hc a)))

lemma portEquiv_seam (p : k.table.Port) (q : l.table.Port)
    (c : k.table.Child p ≃ l.table.Child q)
    (hp : D.atoms ⟨p,none⟩=E.atoms ⟨q,none⟩)
    (hc : ∀ a,D.atoms ⟨p,some a⟩=E.atoms ⟨q,some (c a)⟩) :
    (D.portEquiv p).trans (finCongr (D.rank_of_atoms E hp))=
      (D.seamColumns E p q c hc).trans (E.portEquiv q) := by
  ext i : 1
  apply E.atom_injective ⟨q,none⟩
  exact (D.atom_cast_other E hp (D.rank_of_atoms E hp) (D.portEquiv p i)).trans
    ((D.atom_port p i).trans
      ((D.atom_cast_other E (hc i.1) _ i.2).symm.trans
        (E.atom_port q (D.seamColumns E p q c hc i)).symm))

/-- Ordered atomic block frames agree under named parent and child identifications. -/
lemma frame_seam {R : Type} [CommRing R] (p : k.table.Port) (q : l.table.Port)
    (c : k.table.Child p ≃ l.table.Child q)
    (hp : D.atoms ⟨p,none⟩=E.atoms ⟨q,none⟩)
    (hc : ∀ a,D.atoms ⟨p,some a⟩=E.atoms ⟨q,some (c a)⟩) :
    ((D.frame p (R:=R)).trans (MatrixIso.congr (finCongr (D.rank_of_atoms E hp))))=
      (MatrixIso.congr (D.seamColumns E p q c hc)).trans (E.frame q) := by
  exact (MatrixIso.congr_trans _ _).trans
    ((congrArg (fun e => MatrixIso.congr (R:=R) e) (D.portEquiv_seam E p q c hp hc)).trans
      (MatrixIso.congr_trans _ _).symm)
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
open scoped Classical
variable {A R : Type} [Fintype A] [CommRing R] {k l : Kind}
  (D : AtomicData k A) (E : AtomicData l A)
lemma frame_reindex (p : k.table.Port) (q : l.table.Port)
    (c : k.table.Child p ≃ l.table.Child q)
    (hp : D.atoms ⟨p,none⟩=E.atoms ⟨q,none⟩)
    (hc : ∀ a,D.atoms ⟨p,some a⟩=E.atoms ⟨q,some (c a)⟩) :
    (E.frame q (R:=R)).reindex (D.seamColumns E p q c hc)
      (finCongr (D.rank_of_atoms E hp))=D.frame p := by
  change (MatrixIso.congr _).reindex _ _=MatrixIso.congr _
  rw [MatrixIso.congr_reindex]
  apply congrArg (fun e => MatrixIso.congr (R:=R) e)
  ext i : 1
  apply (finCongr (D.rank_of_atoms E hp)).injective
  exact ((finCongr (D.rank_of_atoms E hp)).apply_symm_apply
    ((E.portEquiv q) ((D.seamColumns E p q c hc) i))).trans
      (congrArg (fun e => e i) (D.portEquiv_seam E p q c hp hc)).symm

/-- Gauge-compatible named atomic seams give frame equalities under the parent and child
identifications. -/
lemma reframe_seam (G : D.localRanks.CoherentBases (R:=R))
    (H : E.localRanks.CoherentBases (R:=R))
    (p : k.table.Port) (q : l.table.Port)
    (c : k.table.Child p ≃ l.table.Child q)
    (hp : D.atoms ⟨p,none⟩=E.atoms ⟨q,none⟩)
    (hc : ∀ a,D.atoms ⟨p,some a⟩=E.atoms ⟨q,some (c a)⟩)
    (hg : (H.basis q none).reindex (finCongr (D.rank_of_atoms E hp))
      (finCongr (D.rank_of_atoms E hp))=G.basis p none)
    (hh : ∀ a,(H.basis q (some (c a))).reindex (finCongr (D.rank_of_atoms E (hc a)))
      (finCongr (D.rank_of_atoms E (hc a)))=G.basis p (some a)) :
    (H.reframe E.frame q).reindex (D.seamColumns E p q c hc)
      (finCongr (D.rank_of_atoms E hp))=G.reframe D.frame p := by
  have hb : (H.columns q).reindex (D.seamColumns E p q c hc)
      (D.seamColumns E p q c hc)=G.columns p := by
    change (MatrixIso.block _).reindex (Equiv.sigmaCongr _ _) (Equiv.sigmaCongr _ _)=_
    rw [MatrixIso.block_reindex_sigma]
    exact congrArg MatrixIso.block (funext hh)
  change ((H.columns q).symm.trans (E.frame q) |>.trans (H.basis q none)).reindex _ _=_
  rw [MatrixIso.bases_reindex,hb,D.frame_reindex E p q c hp hc,hg]
  rfl
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma vertex_frame_seam (v u : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port) (q : (w.shape.atomicBand.kind u).table.Port)
    (c : (w.shape.atomicBand.kind v).table.Child p ≃ (w.shape.atomicBand.kind u).table.Child q)
    (hp : (w.shape.atomicBand.decoration v).color ⟨p,none⟩=
      (w.shape.atomicBand.decoration u).color ⟨q,none⟩)
    (hc : ∀ a,(w.shape.atomicBand.decoration v).color ⟨p,some a⟩=
      (w.shape.atomicBand.decoration u).color ⟨q,some (c a)⟩) :
    (w.vertexFrames u q).reindex
      ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms u) p q c
        (fun a => congrArg w.shape.facetAtoms (hc a)))
      (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms u)
        (congrArg w.shape.facetAtoms hp)))=w.vertexFrames v p := by
  apply (w.shape.vertexAtoms v).reframe_seam (w.shape.vertexAtoms u)
    (w.vertexBases v) (w.vertexBases u) p q c
    (congrArg w.shape.facetAtoms hp) (fun a => congrArg w.shape.facetAtoms (hc a))
  · exact MatrixIso.finite_basis_transport _ w.colorGauge _ _ _ _ _ _ hp _
  · intro a
    exact MatrixIso.finite_basis_transport _ w.colorGauge _ _ _ _ _ _ (hc a) _

def interiorChild (j : Fin w.shape.atomicBand.length) :
    (w.shape.atomicBand.kind j.castSucc).table.Child (w.shape.atomicBand.kind j.castSucc).output ≃
      (w.shape.atomicBand.kind j.succ).table.Child (w.shape.atomicBand.kind j.succ).input :=
  ((w.shape.atomicBand.kind j.castSucc).childEnumeration _).trans
    ((finCongr (w.shape.atomicBand.arity_match j)).trans
      ((w.shape.atomicBand.kind j.succ).childEnumeration _).symm)

lemma interior_parent (j : Fin w.shape.atomicBand.length) :
    (w.shape.atomicBand.decoration j.castSucc).color
      ⟨(w.shape.atomicBand.kind j.castSucc).output,none⟩=
    (w.shape.atomicBand.decoration j.succ).color
      ⟨(w.shape.atomicBand.kind j.succ).input,none⟩ :=
  w.shape.atomicBand.color_match j none

lemma interior_child (j : Fin w.shape.atomicBand.length) (a) :
    (w.shape.atomicBand.decoration j.castSucc).color
      ⟨(w.shape.atomicBand.kind j.castSucc).output,some a⟩=
    (w.shape.atomicBand.decoration j.succ).color
      ⟨(w.shape.atomicBand.kind j.succ).input,some (w.interiorChild j a)⟩ := by
  have hh := w.shape.atomicBand.color_match j
    (some ((w.shape.atomicBand.kind j.castSucc).childEnumeration _ a))
  rw [Decoration.portColor_child] at hh
  exact hh

/-- Internal original-gallery seams are satisfied by the named root bases with identity side
transports. -/
lemma interior_frame_seam (j : Fin w.shape.atomicBand.length) :
    (w.vertexFrames j.succ (w.shape.atomicBand.kind j.succ).input).reindex
      ((w.shape.vertexAtoms j.castSucc).seamColumns (w.shape.vertexAtoms j.succ)
        _ _ (w.interiorChild j)
        (fun a => congrArg w.shape.facetAtoms (w.interior_child j a)))
      (finCongr ((w.shape.vertexAtoms j.castSucc).rank_of_atoms (w.shape.vertexAtoms j.succ)
        (congrArg w.shape.facetAtoms (w.interior_parent j))))=
      w.vertexFrames j.castSucc (w.shape.atomicBand.kind j.castSucc).output :=
  w.vertex_frame_seam _ _ _ _ _ (w.interior_parent j) (w.interior_child j)
end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

end OAI
