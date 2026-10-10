import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.NamedSeams
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BandCut

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
def portNamedColumns (p : LocalPort V D.ports.kind) :
    ((i : Fin (arity (D.ports.attach p).1)) × Fin (D.childDim (D.ports.attach p).1 i)) ≃
      (D.vertexRanks p.1).Columns p.2 :=
  (Equiv.sigmaCongr (D.ports.childEquiv p) (fun _ => Equiv.refl _)).symm

def portChildMatch (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.ports.kind p.1).table.Child p.2 ≃ (D.ports.kind u.1).table.Child u.2 :=
  (D.ports.childEquiv p).trans ((finCongr (congrArg arity h)).trans (D.ports.childEquiv u).symm)
lemma portParentRank_match (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.vertexRanks p.1).rank p.2 none=(D.vertexRanks u.1).rank u.2 none :=
  congrArg (fun s=>D.rank (D.ports.facet ⟨s,none⟩)) h
lemma side_child_congr {s t : S} (h : s=t) (i : Fin (arity s)) :
    (⟨s,some i⟩ : Side S arity)=⟨t,some (finCongr (congrArg arity h) i)⟩ := by
  subst t
  rfl
lemma portChildRank_match (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) (c) :
    (D.vertexRanks p.1).rank p.2 (some c)=
      (D.vertexRanks u.1).rank u.2 (some (D.portChildMatch p u h c)) := by
  change D.rank (D.ports.facet ⟨(D.ports.attach p).1,some ((D.ports.childEquiv p) c)⟩)=
    D.rank (D.ports.facet ⟨(D.ports.attach u).1,some ((D.ports.childEquiv u)
      ((D.ports.childEquiv u).symm (finCongr (congrArg arity h) ((D.ports.childEquiv p) c))))⟩)
  rw [Equiv.apply_symm_apply]
  exact congrArg (fun s=>D.rank (D.ports.facet s)) (side_child_congr h _)
def portColumnMatch (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.vertexRanks p.1).Columns p.2 ≃ (D.vertexRanks u.1).Columns u.2 :=
  Equiv.sigmaCongr (D.portChildMatch p u h) (fun c=>finCongr (D.portChildRank_match p u h c))
def portParentMatch (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.vertexRanks p.1).Parent p.2 ≃ (D.vertexRanks u.1).Parent u.2 :=
  finCongr (D.portParentRank_match p u h)
def namedColumnsMatch {s t : S} (h : s=t) :
    ((i : Fin (arity s)) × Fin (D.childDim s i)) ≃
      ((i : Fin (arity t)) × Fin (D.childDim t i)) :=
  Equiv.sigmaCongr (finCongr (congrArg arity h)) (fun i=>
    finCongr (congrArg (fun a=>D.rank (D.ports.facet a)) (side_child_congr h i)))
lemma namedColumnsMatch_refl (s : S) : D.namedColumnsMatch (s:=s) rfl=Equiv.refl _ := by
  apply Equiv.ext
  intro i
  apply Sigma.ext (by rfl)
  apply (Fin.heq_ext_iff rfl).mpr
  rfl
lemma portColumnMatch_named_forward (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.portColumnMatch p u h).trans (D.portNamedColumns u).symm=
      (D.portNamedColumns p).symm.trans (D.namedColumnsMatch h) := by
  apply Equiv.ext
  intro i
  have hh : (((D.portColumnMatch p u h).trans (D.portNamedColumns u).symm) i).1=
      (((D.portNamedColumns p).symm.trans (D.namedColumnsMatch h)) i).1 := by
    change (D.ports.childEquiv u) ((D.ports.childEquiv u).symm
      (finCongr (congrArg arity h) ((D.ports.childEquiv p) i.1)))=_
    exact Equiv.apply_symm_apply _ _
  apply Sigma.ext hh
  apply (Fin.heq_ext_iff (congrArg (D.childDim (D.ports.attach u).1) hh)).mpr
  rfl
lemma portColumnMatch_named (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    ((D.portNamedColumns p).symm.trans (D.namedColumnsMatch h)).trans (D.portNamedColumns u)=
      D.portColumnMatch p u h := by
  rw [←D.portColumnMatch_named_forward p u h, Equiv.trans_assoc,
    Equiv.symm_trans_self,Equiv.trans_refl]
lemma portColumnMatch_named_left (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.portNamedColumns p).trans (D.portColumnMatch p u h)=
      (D.namedColumnsMatch h).trans (D.portNamedColumns u) := by
  rw [←D.portColumnMatch_named p u h]
  apply Equiv.ext
  intro i
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
lemma namedColumnsMatch_index {s t : S} (h : s=t) :
    (D.namedColumnsMatch h).trans (blockIndex (D.childDim t)).symm=
      ((blockIndex (D.childDim s)).symm).trans (finCongr (congrArg D.seamDim h)) := by
  subst t
  erw [D.namedColumnsMatch_refl]
  have he : finCongr (congrArg D.seamDim (rfl : s=s))=Equiv.refl _ := by ext i; rfl
  erw [he]
  rfl
lemma portColumnMatch_index (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.portColumnMatch p u h).trans (D.portColumnIndex u)=
      (D.portColumnIndex p).trans (finCongr (congrArg D.seamDim h)) := by
  rw [←D.portColumnMatch_named p u h]
  change ((((D.portNamedColumns p).symm.trans (D.namedColumnsMatch h)).trans
    (D.portNamedColumns u)).trans ((D.portNamedColumns u).symm.trans (blockIndex (D.childDim _)).symm))=
    (((D.portNamedColumns p).symm.trans (blockIndex (D.childDim _)).symm).trans _)
  erw [Equiv.trans_assoc,Equiv.trans_assoc,←Equiv.trans_assoc (D.portNamedColumns u),
    Equiv.self_trans_symm,Equiv.refl_trans, D.namedColumnsMatch_index h]
  exact (Equiv.trans_assoc _ _ _).symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity)
lemma portColumnMatch_from_index (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.portColumnIndex p).symm.trans (D.portColumnMatch p u h)=
      (finCongr (congrArg D.seamDim h)).trans (D.portColumnIndex u).symm := by
  apply Equiv.ext
  intro i
  apply (D.portColumnIndex u).injective
  have hh := Equiv.congr_fun (D.portColumnMatch_index p u h) ((D.portColumnIndex p).symm i)
  simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using hh
lemma portParentMatch_from_index (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1) :
    (D.portRowIndex p).symm.trans (D.portParentMatch p u h)=
      (finCongr (congrArg D.seamDim h)).trans (D.portRowIndex u).symm := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties
variable {R V W α : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] {a : α → ℕ}
namespace SameFramedFlag
variable {f g h : (α → R) ≃ₗ[R] V}
lemma refl (f : (α → R) ≃ₗ[R] V) : SameFramedFlag a f f := ⟨fun _ => rfl,fun _ _ _ => rfl⟩
lemma symm (hf : SameFramedFlag a f g) : SameFramedFlag a g f := by
  refine ⟨fun k => (hf.1 k).symm,?_⟩
  intro k v hv
  rw [← hf.1 (k+1)] at hv
  exact (hf.2 k v hv).symm
lemma trans (hf : SameFramedFlag a f g) (hg : SameFramedFlag a g h) : SameFramedFlag a f h := by
  refine ⟨fun k => (hf.1 k).trans (hg.1 k),?_⟩
  intro k v hv
  exact (hf.2 k v hv).trans (hg.2 k v ((hf.1 (k+1)) ▸ hv))
/-- Parent transport preserves the named grade maps. -/
lemma postcompose (hf : SameFramedFlag a f g) (e : V ≃ₗ[R] W) :
    SameFramedFlag a (f.trans e) (g.trans e) := by
  constructor
  · intro k
    change (coordinatePrefix R a k).map (e.toLinearMap.comp f.toLinearMap)=
      (coordinatePrefix R a k).map (e.toLinearMap.comp g.toLinearMap)
    rw [Submodule.map_comp,Submodule.map_comp]
    exact congrArg (fun U : Submodule R V => U.map e.toLinearMap) (hf.1 k)
  · intro k v hv
    change v∈(coordinatePrefix R a (k+1)).map (e.toLinearMap.comp f.toLinearMap) at hv
    rw [Submodule.map_comp] at hv
    rcases hv with ⟨u,hu,rfl⟩
    change coordinateGrade R a k (f.symm (e.symm (e u)))=
      coordinateGrade R a k (g.symm (e.symm (e u)))
    rw [LinearEquiv.symm_apply_apply]
    exact hf.2 k u hu
end SameFramedFlag
end IntegralCharacterVarieties
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
open scoped Classical
variable {A R : Type} [Fintype A] [CommRing R] {k l : Kind}
  (D : AtomicData k A) (E : AtomicData l A)
lemma reframe_seam_post (G : D.localRanks.CoherentBases (R:=R))
    (H : E.localRanks.CoherentBases (R:=R))
    (p : k.table.Port) (q : l.table.Port)
    (c : k.table.Child p ≃ l.table.Child q)
    (hp : D.atoms ⟨p,none⟩=E.atoms ⟨q,none⟩)
    (hc : ∀ a,D.atoms ⟨p,some a⟩=E.atoms ⟨q,some (c a)⟩)
    (Z : MatrixIso R (D.localRanks.Parent p) (D.localRanks.Parent p))
    (hg : (H.basis q none).reindex (finCongr (D.rank_of_atoms E hp))
      (finCongr (D.rank_of_atoms E hp))=(G.basis p none).trans Z)
    (hh : ∀ a,(H.basis q (some (c a))).reindex (finCongr (D.rank_of_atoms E (hc a)))
      (finCongr (D.rank_of_atoms E (hc a)))=G.basis p (some a)) :
    (H.reframe E.frame q).reindex (D.seamColumns E p q c hc)
      (finCongr (D.rank_of_atoms E hp))=(G.reframe D.frame p).trans Z := by
  have hb : (H.columns q).reindex (D.seamColumns E p q c hc)
      (D.seamColumns E p q c hc)=G.columns p := by
    change (MatrixIso.block _).reindex (Equiv.sigmaCongr _ _) (Equiv.sigmaCongr _ _)=_
    rw [MatrixIso.block_reindex_sigma]
    exact congrArg MatrixIso.block (funext hh)
  change ((H.columns q).symm.trans (E.frame q) |>.trans (H.basis q none)).reindex _ _=_
  rw [MatrixIso.bases_reindex,hb,D.frame_reindex E p q c hp hc,hg]
  exact (MatrixIso.trans_assoc _ _ _).symm
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData

namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)
lemma mirror_basis_at_color (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) (z)
    (c : Option (Secondary n n)) (hc : (w.shape.atomicBand.decoration v).color z=c)
    (hr : (w.shape.vertexAtoms v).rank z=freshRank r w.shape.secondaryRank c) :
    ((w.mirrorVertexBases T v).basis ((w.shape.atomicBand.kind v).mirrorEnd z).1
      ((w.shape.atomicBand.kind v).mirrorEnd z).2).reindex
        (finCongr ((w.shape.vertexAtoms v).mirror.rank_of_atoms (w.shape.vertexAtoms v)
          ((w.shape.vertexAtoms v).mirror_atoms z) |>.trans hr)).symm
        (finCongr ((w.shape.vertexAtoms v).mirror.rank_of_atoms (w.shape.vertexAtoms v)
          ((w.shape.vertexAtoms v).mirror_atoms z) |>.trans hr)).symm =
      w.mirrorColorGauge T c := by
  let e := (w.shape.atomicBand.kind v).mirrorEnd
  have he : (w.shape.atomicBand.decoration v).color (e.symm (e z))=c :=
    (congrArg (w.shape.atomicBand.decoration v).color (e.symm_apply_apply z)).trans hc
  have hh := MatrixIso.finite_basis_transport (freshRank r w.shape.secondaryRank) (w.mirrorColorGauge T)
    c ((w.shape.atomicBand.decoration v).color (e.symm (e z)))
    (freshRank r w.shape.secondaryRank c) ((w.shape.vertexAtoms v).mirror.rank (e z))
    rfl (w.shape.vertexAtoms_rank v (e.symm (e z))) he.symm
    (((w.shape.vertexAtoms v).mirror.rank_of_atoms (w.shape.vertexAtoms v)
      ((w.shape.vertexAtoms v).mirror_atoms z)).trans hr).symm
  simp only [finCongr_refl,MatrixIso.reindex_refl_eq] at hh
  exact hh

lemma mirror_principal_basis (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : (w.shape.atomicBand.decoration v).color ⟨p,none⟩=none)
    (hr : (w.shape.vertexAtoms v).rank ⟨p,none⟩=r) :
    ((w.mirrorVertexBases T v).basis ((w.shape.atomicBand.kind v).mirrorPort p) none).reindex
      (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
        ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm))
      (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
        ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm))=
      ((w.vertexBases v).basis p none).trans
        (T.symm.reindex (finCongr hr) (finCongr hr)) := by
  have hm := w.mirror_basis_at_color T v ⟨p,none⟩ none hp hr
  have ho := w.basis_at_color v p none none hp hr
  have hh := congrArg (fun g : MatrixIso K (Fin r) (Fin r) =>
      g.reindex (finCongr hr) (finCongr hr)) hm
  have ho' := congrArg (fun g : MatrixIso K (Fin r) (Fin r) =>
      g.reindex (finCongr hr) (finCongr hr)) ho
  change (w.vertexBases v).basis p none=
    (w.colorGauge none).reindex (finCongr hr) (finCongr hr) at ho'
  change _=(w.colorGauge none |>.trans T.symm).reindex (finCongr hr) (finCongr hr) at hh
  erw [MatrixIso.reindex_trans _ _ (finCongr hr) (finCongr hr) (finCongr hr),←ho'] at hh
  exact hh

lemma mirror_principal_frame (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : (w.shape.atomicBand.decoration v).color ⟨p,none⟩=none)
    (hr : (w.shape.vertexAtoms v).rank ⟨p,none⟩=r) :
    (w.mirrorVertexFrames T v ((w.shape.atomicBand.kind v).mirrorPort p)).reindex
      ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror p
        ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p)
        (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm))
      (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
        ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm))=
      (w.vertexFrames v p).trans (T.symm.reindex (finCongr hr) (finCongr hr)) := by
  apply (w.shape.vertexAtoms v).reframe_seam_post (w.shape.vertexAtoms v).mirror
    (w.vertexBases v) (w.mirrorVertexBases T v) p ((w.shape.atomicBand.kind v).mirrorPort p)
    ((w.shape.atomicBand.kind v).mirrorChild p)
    ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm
    (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm)
  · exact w.mirror_principal_basis T v p hp hr
  · intro a
    exact w.mirror_basis T v ⟨p,some a⟩ (w.child_color_ne v p a)

/-- The mirror frame in the coordinate labels of the original port. -/
def mirrorAlignedFrame (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) (p : (w.shape.atomicBand.kind v).table.Port) :=
  (w.mirrorVertexFrames T v ((w.shape.atomicBand.kind v).mirrorPort p)).reindex
    ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror p
      ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p)
      (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm))
    (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
      ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm))

lemma mirror_canonical_frame (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) (p : (w.shape.atomicBand.kind v).table.Port)
    (hp : (w.shape.atomicBand.decoration v).color ⟨p,none⟩=none)
    (hr : (w.shape.vertexAtoms v).rank ⟨p,none⟩=r)
    {A : Type} [Fintype A] (e : A ≃ (w.shape.vertexAtoms v).localRanks.Columns p) :
    ((w.mirrorAlignedFrame T v p).reindex e (finCongr hr).symm).linearEquiv=
      (((w.vertexFrames v p).reindex e (finCongr hr).symm).linearEquiv).trans T.symm.linearEquiv := by
  have hh : w.mirrorAlignedFrame T v p=(w.vertexFrames v p).trans
      (T.symm.reindex (finCongr hr) (finCongr hr)) := w.mirror_principal_frame T v p hp hr
  erw [hh,MatrixIso.reindex_trans _ _ e (finCongr hr).symm (finCongr hr).symm]
  ext v i
  exact congrFun (MatrixIso.linearEquiv_trans_apply _ _ v) i

def mirrorFirstFrame (T : MatrixIso K (Fin r) (Fin r)) :=
  ((w.mirrorAlignedFrame T 0 (w.shape.atomicBand.kind 0).input).reindex
    w.firstColumns.symm (finCongr w.firstParent_rank).symm).linearEquiv

def mirrorLastFrame (T : MatrixIso K (Fin r) (Fin r)) :=
  ((w.mirrorAlignedFrame T (Fin.last w.shape.atomicBand.length)
    (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output).reindex
    w.lastColumns.symm (finCongr w.lastParent_rank).symm).linearEquiv

lemma mirrorFirstFrame_eq (T : MatrixIso K (Fin r) (Fin r)) :
    w.mirrorFirstFrame T=w.firstFrame.trans T.symm.linearEquiv :=
  w.mirror_canonical_frame T 0 _ w.shape.atomicBand.input_parent w.firstParent_rank w.firstColumns.symm

lemma mirrorLastFrame_eq (T : MatrixIso K (Fin r) (Fin r)) :
    w.mirrorLastFrame T=w.lastFrame.trans T.symm.linearEquiv :=
  w.mirror_canonical_frame T (Fin.last _) _ w.shape.atomicBand.output_parent w.lastParent_rank w.lastColumns.symm

lemma mirrorFirstFrame_holds (T : MatrixIso K (Fin r) (Fin r)) :
    SameFramedFlag (fun i : (i : Fin n) × Fin (s i) => i.1.val)
      (w.mirrorFirstFrame T) (f.trans T.symm.linearEquiv) := by
  rw [w.mirrorFirstFrame_eq]
  exact w.firstFrame_holds.postcompose T.symm.linearEquiv

lemma mirrorLastFrame_holds (T : MatrixIso K (Fin r) (Fin r)) :
    SameFramedFlag (fun i : (i : Fin n) × Fin (s i) => i.1.val)
      (w.mirrorLastFrame T) (h.trans T.symm.linearEquiv) := by
  rw [w.mirrorLastFrame_eq]
  exact w.lastFrame_holds.postcompose T.symm.linearEquiv
end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
variable {K : Type} [Field K] {n r : ℕ} (s : Fin n → ℕ)
variable (f g : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K))
    (P J : (Fin r → K) ≃ₗ[K] (Fin r → K))
    (T : MatrixIso K (Fin r) (Fin r))
    (U : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (((i : Fin n) × Fin (s i)) → K))
variable (w : IdentifiedBand s f ((f.trans P).trans J.symm))

/-- The short seam at the original negative endpoint has identity parent and child transports and
preserves each named quotient. -/
lemma cut_short_first : SameFramedFlag (fun i : ((i : Fin n) × Fin (s i)) => i.1.val) f w.firstFrame := w.firstFrame_holds.symm

/-- The original child transports remain on the positive port, while the last frame is transported
by the cut handle coordinate J. -/
lemma cut_short_last (hold : SameFramedFlag (fun i : ((i : Fin n) × Fin (s i)) => i.1.val) (f.trans P) (U.trans g)) :
    SameFramedFlag (fun i : ((i : Fin n) × Fin (s i)) => i.1.val) (w.lastFrame.trans J) (U.trans g) := by
  have hh := w.lastFrame_holds.postcompose J
  have he : ((f.trans P).trans J.symm).trans J=f.trans P := by ext v i; simp
  rw [he] at hh
  exact hh.trans hold

/-- The inner boundary is the inverse-cut word T⁻¹ J⁻¹ P T. -/
def cutInnerLinear : (Fin r → K) ≃ₗ[K] (Fin r → K) :=
  ((T.linearEquiv.trans P).trans J.symm).trans T.symm.linearEquiv

lemma cutInner_after_mirror :
    (f.trans T.symm.linearEquiv).trans (cutInnerLinear (r:=r) P J T)=
      ((f.trans P).trans J.symm).trans T.symm.linearEquiv := by
  ext v i
  change T.symm.linearEquiv (J.symm (P (T.linearEquiv (T.symm.linearEquiv (f v))))) i=_
  have he (x : Fin r → K) : T.linearEquiv (T.symm.linearEquiv x)=x := by
    exact T.linearEquiv.apply_symm_apply x
  rw [he]
  rfl

/-- The mirror wraps in the opposite direction with principal basis T⁻¹. -/
lemma cut_short_mirror : SameFramedFlag (fun i : ((i : Fin n) × Fin (s i)) => i.1.val)
    ((w.mirrorFirstFrame T).trans (cutInnerLinear (r:=r) P J T)) (w.mirrorLastFrame T) := by
  have hf := (w.mirrorFirstFrame_holds T).postcompose (cutInnerLinear (r:=r) P J T)
  rw [cutInner_after_mirror s f P J T] at hf
  exact hf.trans (w.mirrorLastFrame_holds T).symm
end IntegralCharacterVarieties.NamedBandGrades
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression HomTransport
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity)
/-- Framed-flag transport respecting the seam child enumeration. -/
lemma localFrameFlag_match (f : D.PortFrames (R:=R))
    (p u : LocalPort V D.ports.kind)
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (hs : SameFramedFlag (fun i => D.seamGrade (D.ports.attach p).1 (D.portColumnIndex p i))
      (f p).linearEquiv
      ((f u).reindex (D.portColumnMatch p u h) (D.portParentMatch p u h)).linearEquiv) :
    SameFramedFlag (D.seamGrade (D.ports.attach p).1)
      (MatrixIso.unit (D.localFrameUnit f p)).linearEquiv
      ((MatrixIso.unit (D.localFrameUnit f u)).reindex
        (finCongr (congrArg D.seamDim h)) (finCongr (congrArg D.seamDim h))).linearEquiv := by
  have hx : (MatrixIso.unit (D.localFrameUnit f p)).reindex
      (D.portColumnIndex p) (D.portRowIndex p)=f p := by
    simp only [localFrameUnit,MatrixIso.unit_toUnit,MatrixIso.reindex_reindex_eq,
      Equiv.self_trans_symm,MatrixIso.reindex_refl_eq]
  have hy : ((MatrixIso.unit (D.localFrameUnit f u)).reindex
      (finCongr (congrArg D.seamDim h)) (finCongr (congrArg D.seamDim h))).reindex
      (D.portColumnIndex p) (D.portRowIndex p)=
      (f u).reindex (D.portColumnMatch p u h) (D.portParentMatch p u h) := by
    simp only [localFrameUnit,MatrixIso.unit_toUnit,MatrixIso.reindex_reindex_eq,
      ←D.portColumnMatch_from_index p u h,←D.portParentMatch_from_index p u h,
      ←Equiv.trans_assoc,Equiv.self_trans_symm,Equiv.refl_trans]
  apply (MatrixIso.sameFramedFlag_reindex_iff _ _ _
    (D.portColumnIndex p) (D.portRowIndex p)).mp
  rw [hx,hy]
  exact hs
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression HomTransport
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity)
/-- Attached negative and positive ports determine the seam framed-flag condition. -/
lemma frameValues_seam_flag_of_ports (f : D.PortFrames (R:=R))
    (p u : LocalPort V D.ports.kind) (s : S)
    (hp : D.ports.attach p=(s,false)) (hu : D.ports.attach u=(s,true))
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (hs : SameFramedFlag (fun i => D.seamGrade (D.ports.attach p).1 (D.portColumnIndex p i))
      (f p).linearEquiv
      ((f u).reindex (D.portColumnMatch p u h) (D.portParentMatch p u h)).linearEquiv) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv (D.frameValues f s false))
      (matrixUnitEquiv (D.frameValues f s true)) := by
  have hh := D.localFrameFlag_match f p u h hs
  rw [←D.frameValues_attach,←D.frameValues_attach] at hh
  have aux {a b : S × Bool} (ha : a=(s,false)) (hb : b=(s,true))
      (he : a.1=b.1)
      (ht : SameFramedFlag (D.seamGrade a.1)
        (MatrixIso.unit (D.frameValues f a.1 a.2)).linearEquiv
        ((MatrixIso.unit (D.frameValues f b.1 b.2)).reindex
          (finCongr (congrArg D.seamDim he)) (finCongr (congrArg D.seamDim he))).linearEquiv) :
      SameFramedFlag (D.seamGrade s)
        (matrixUnitEquiv (D.frameValues f s false))
        (matrixUnitEquiv (D.frameValues f s true)) := by
    subst a
    subst b
    simpa only [finCongr_refl,MatrixIso.reindex_refl_eq,MatrixIso.unit_linearEquiv] using ht
  exact aux hp hu h hh
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R α β α' β' : Type*} [CommRing R] [Fintype α] [Fintype β]
    [Fintype α'] [Fintype β']
lemma sameFramedFlag_of_coordinates (a : α → ℕ) (x y : MatrixIso R α β)
    (e : α' ≃ α) (f : β' ≃ β) (a' : α' → ℕ)
    (x' y' : (α' → R) ≃ₗ[R] (β' → R))
    (ha : ∀ i,a (e i)=a' i)
    (hx : (x.reindex e f).linearEquiv=x')
    (hy : (y.reindex e f).linearEquiv=y')
    (hh : SameFramedFlag a' x' y') :
    SameFramedFlag a x.linearEquiv y.linearEquiv := by
  apply (sameFramedFlag_reindex_iff a x y e f).mp
  rw [hx,hy,show (fun i=>a (e i))=a' from funext ha]
  exact hh
variable {γ δ : Type*} [Fintype γ] [Fintype δ]
lemma sameFramedFlag_of_matching_coordinates (a : α → ℕ)
    (x : MatrixIso R α β) (y : MatrixIso R γ δ)
    (m : α ≃ γ) (n : β ≃ δ)
    (e : α' ≃ α) (f : β' ≃ β) (em : α' ≃ γ) (fn : β' ≃ δ)
    (he : e.trans m=em) (hf : f.trans n=fn) (a' : α' → ℕ)
    (x' y' : (α' → R) ≃ₗ[R] (β' → R))
    (ha : ∀ i,a (e i)=a' i)
    (hx : (x.reindex e f).linearEquiv=x')
    (hy : (y.reindex em fn).linearEquiv=y')
    (hh : SameFramedFlag a' x' y') :
    SameFramedFlag a x.linearEquiv (y.reindex m n).linearEquiv := by
  apply sameFramedFlag_of_coordinates a x (y.reindex m n) e f a' x' y' ha hx _ hh
  rw [reindex_reindex_eq,he,hf]
  exact hy
end IntegralCharacterVarieties.MatrixIso
end

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R α β γ : Type*} [CommRing R]
    [Fintype α] [Fintype β] [Fintype γ]
lemma linearEquiv_trans_eq (x : MatrixIso R α β) (y : MatrixIso R β γ) :
    (x.trans y).linearEquiv=x.linearEquiv.trans y.linearEquiv := by
  ext v i
  exact congrFun (linearEquiv_trans_apply x y v) i
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (s : S) (φ : R →+* K)
    (g : (e : D.Generator) →
      (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    {α β : Type*} [Fintype α] [Fintype β]
/-- Reindex all four factors of a seam into common coordinates, including the parent and child
transports. -/
lemma seamHolds_of_coordinates
    (e : α ≃ Fin (D.seamDim s)) (f : β ≃ Fin (D.seamDim s))
    (a : α → ℕ) (x y : (α → K) ≃ₗ[K] (β → K))
    (p : (β → K) ≃ₗ[K] (β → K)) (u : (α → K) ≃ₗ[K] (α → K))
    (ha : ∀ i,D.seamGrade s (e i)=a i)
    (hx : ((MatrixIso.unit (g (.frame s false))).reindex e f).linearEquiv=x)
    (hy : ((MatrixIso.unit (g (.frame s true))).reindex e f).linearEquiv=y)
    (hp : ((MatrixIso.unit ((D.parentWord s).eval φ g)).reindex f f).linearEquiv=p)
    (hu : ((MatrixIso.unit ((Term.block (D.childDim s)
      (fun j => Term.inv (D.childWord s j))).eval φ g)).reindex e e).linearEquiv=u)
    (hh : SameFramedFlag a (x.trans p) (u.trans y)) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ g))
      (matrixUnitEquiv ((D.seamRight s).eval φ g)) := by
  apply MatrixIso.sameFramedFlag_of_coordinates (D.seamGrade s)
    (MatrixIso.unit ((D.seamLeft s).eval φ g))
    (MatrixIso.unit ((D.seamRight s).eval φ g)) e f a (x.trans p) (u.trans y) ha
  · simp only [seamLeft, Term.eval, frameWord]
    erw [MatrixIso.unit_mul, MatrixIso.reindex_trans _ _ e f f,
      MatrixIso.linearEquiv_trans_eq, hx, hp]
  · simp only [seamRight, Term.eval, frameWord]
    erw [MatrixIso.unit_mul, MatrixIso.reindex_trans _ _ e e f,
      MatrixIso.linearEquiv_trans_eq, hy]
    exact congrArg (fun z => z.trans y) hu
  · exact hh

/-- Transport of the parent word over its coefficient ring. -/
lemma parentWord_coordinates {n : ℕ}
    (h : D.rank (D.ports.facet ⟨s,none⟩)=n)
    (p : (Matrix (Fin n) (Fin n) K)ˣ)
    (hp : rebaseUnit h (g (.side ⟨s,none⟩))=p)
    (f : Fin n ≃ Fin (D.seamDim s))
    (hf : f=finCongr (h.symm.trans (D.seamRank s))) :
    ((MatrixIso.unit ((D.parentWord s).eval φ g)).reindex f f).linearEquiv=
      (MatrixIso.unit p).linearEquiv := by
  rw [hf]
  unfold parentWord
  erw [Term.eval_cast_unit φ g (D.seamRank s)]
  simp only [sideWord,Term.eval]
  erw [rebaseUnit_iso,MatrixIso.reindex_reindex_eq]
  have he : (finCongr (h.symm.trans (D.seamRank s))).trans
      (finCongr (D.seamRank s).symm)=finCongr h.symm := by
    ext i
    rfl
  erw [he,←rebaseUnit_iso h, hp]

/-- A block child inverse preserves named fibers under a child-index identification over the
coefficient ring. -/
lemma childWord_coordinates {m : ℕ} (d : Fin m → ℕ)
    (c : Fin m ≃ Fin (arity s))
    (hc : ∀ i,d i=D.childDim s (c i))
    (old : (i : Fin m) → (Matrix (Fin (d i)) (Fin (d i)) K)ˣ)
    (ho : ∀ i,rebaseUnit (hc i).symm (g (.side ⟨s,some (c i)⟩))=old i)
    (e : ((i : Fin m) × Fin (d i)) ≃ Fin (D.seamDim s))
    (he : e=(Equiv.sigmaCongr c (fun i=>finCongr (hc i))).trans
      (blockIndex (D.childDim s)).symm) :
    ((MatrixIso.unit ((Term.block (D.childDim s)
      (fun j => Term.inv (D.childWord s j))).eval φ g)).reindex e e).linearEquiv=
      (MatrixIso.block (fun i=>MatrixIso.unit (old i)⁻¹)).linearEquiv := by
  simp only [Term.eval,childWord,sideWord]
  erw [MatrixIso.unit_block,MatrixIso.reindex_reindex_eq,he]
  have he' : ((Equiv.sigmaCongr c (fun i=>finCongr (hc i))).trans
      (blockIndex (D.childDim s)).symm).trans (blockIndex (D.childDim s))=
      Equiv.sigmaCongr c (fun i=>finCongr (hc i)) := by
    rw [Equiv.trans_assoc,Equiv.symm_trans_self,Equiv.trans_refl]
  erw [he',MatrixIso.block_reindex_sigma]
  have hb (i : Fin m) : (MatrixIso.unit (g (.side ⟨s,some (c i)⟩))⁻¹).reindex
      (finCongr (hc i)) (finCongr (hc i))=MatrixIso.unit (old i)⁻¹ := by
    have hh := congrArg (fun z => MatrixIso.unit z⁻¹) (ho i)
    erw [←map_inv,rebaseUnit_iso] at hh
    convert! hh using 1
  convert! congrArg (fun B : (i : Fin m) → MatrixIso K (Fin (d i)) (Fin (d i)) =>
    (MatrixIso.block B).linearEquiv) (funext hb) using 1

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
