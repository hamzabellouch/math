import OAI.AlgebraicGeometry.CharacterVarieties.Frames.BandGauges

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma basis_at_color (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (a : Option ((w.shape.atomicBand.kind v).table.Child p))
    (c : Option (Secondary n n)) (hc : (w.shape.atomicBand.decoration v).color ⟨p,a⟩=c)
    (hr : (w.shape.vertexAtoms v).rank ⟨p,a⟩=freshRank r w.shape.secondaryRank c) :
    ((w.vertexBases v).basis p a).reindex (finCongr hr).symm (finCongr hr).symm=w.colorGauge c := by
  have hh := MatrixIso.finite_basis_transport (freshRank r w.shape.secondaryRank) w.colorGauge
    c ((w.shape.atomicBand.decoration v).color ⟨p,a⟩)
    (freshRank r w.shape.secondaryRank c) ((w.shape.vertexAtoms v).rank ⟨p,a⟩)
    rfl (w.shape.vertexAtoms_rank v ⟨p,a⟩) hc.symm hr.symm
  change (((w.colorGauge ((w.shape.atomicBand.decoration v).color ⟨p,a⟩)).reindex
    (finCongr (w.shape.vertexAtoms_rank v ⟨p,a⟩))
    (finCongr (w.shape.vertexAtoms_rank v ⟨p,a⟩))).reindex
    (finCongr hr.symm) (finCongr hr.symm))=w.colorGauge c
  simpa only [finCongr_refl,MatrixIso.reindex_refl_eq] using hh

lemma firstArity : (w.shape.atomicBand.kind 0).arity (w.shape.atomicBand.kind 0).input=n := by
  have hh := congrArg List.length w.shape.atomicBand.input_children
  simpa only [Decoration.children_length,List.length_map,List.length_ofFn] using hh

def firstChild : (w.shape.atomicBand.kind 0).table.Child (w.shape.atomicBand.kind 0).input ≃ Fin n :=
  ((w.shape.atomicBand.kind 0).childEnumeration _).trans (finCongr w.firstArity)

lemma firstChild_color (c) : (w.shape.atomicBand.decoration 0).color
    ⟨(w.shape.atomicBand.kind 0).input,some c⟩=some (.row (w.firstChild c)) := by
  let i := ((w.shape.atomicBand.kind 0).childEnumeration _ c)
  have hh := congrArg (fun l : List (Option (Secondary n n)) => l[i.val]?)
    w.shape.atomicBand.input_children
  have hi : i.val<n := i.isLt.trans_eq w.firstArity
  simp only [Decoration.children,List.map_ofFn,List.getElem?_ofFn,dite_eq_left i.isLt,dite_eq_left hi] at hh
  exact (Decoration.portColor_child _ _ c).symm.trans (Option.some.inj hh)

lemma firstParent_rank : (w.shape.vertexAtoms 0).rank ⟨(w.shape.atomicBand.kind 0).input,none⟩=r := by
  exact (w.shape.vertexAtoms_rank 0 _).trans
    (congrArg (freshRank r w.shape.secondaryRank) w.shape.atomicBand.input_parent)

lemma firstChild_rank (c) : (w.shape.vertexAtoms 0).rank
    ⟨(w.shape.atomicBand.kind 0).input,some c⟩=s (w.firstChild c) :=
  (w.shape.vertexAtoms_rank 0 _).trans
    ((congrArg (freshRank r w.shape.secondaryRank) (w.firstChild_color c)).trans
      (w.rowRanks (w.firstChild c)).symm)

def firstColumns : (w.shape.vertexAtoms 0).localRanks.Columns (w.shape.atomicBand.kind 0).input ≃
    ((i : Fin n) × Fin (s i)) :=
  Equiv.sigmaCongr w.firstChild (fun c => finCongr (w.firstChild_rank c))

def firstFrame : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K) :=
  ((w.vertexFrames 0 (w.shape.atomicBand.kind 0).input).reindex
    w.firstColumns.symm (finCongr w.firstParent_rank).symm).linearEquiv

end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
lemma linearEquiv_block {ι : Type*} [Fintype ι] {a b : ι → Type*}
    [∀ i,Fintype (a i)] [∀ i,Fintype (b i)]
    (f : ∀ i,MatrixIso R (a i) (b i)) (x : ((i : ι) × a i) → R) (i : ι) (j : b i) :
    (block f).linearEquiv x ⟨i,j⟩=(f i).linearEquiv (fun t => x ⟨i,t⟩) j := by
  change ∑ t,Matrix.blockDiagonal' (fun i => (f i).val) ⟨i,j⟩ t*x t=_
  rw [Fintype.sum_sigma]
  simp [Matrix.blockDiagonal',MatrixIso.linearEquiv,Matrix.toLin'_apply,Matrix.mulVec,dotProduct]
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
open scoped Classical
variable {R A : Type} [CommRing R] [Fintype A] {k : Kind}
    (D : AtomicData k A) (G : D.localRanks.CoherentBases (R:=R))
lemma reframe_inverse (p : k.table.Port) (v : D.localRanks.Parent p → R)
    (c : k.table.Child p) (i : Fin (D.rank ⟨p,some c⟩)) :
    (G.reframe D.frame p).linearEquiv.symm v ⟨c,i⟩=
      (G.basis p (some c)).linearEquiv
        (fun j => (G.basis p none).linearEquiv.symm v (D.portEquiv p ⟨c,j⟩)) i := by
  rw [LocalRanks.CoherentBases.reframe,MatrixIso.linearEquiv_trans_symm_apply,
    MatrixIso.linearEquiv_trans_symm_apply]
  change (MatrixIso.block (fun a => G.basis p (some a))).linearEquiv _ ⟨c,i⟩=_
  refine (MatrixIso.linearEquiv_block (fun a => G.basis p (some a))
    ((D.frame p).linearEquiv.symm ((G.basis p none).linearEquiv.symm v)) c i).trans ?_
  apply congrArg (fun x => (G.basis p (some c)).linearEquiv x i)
  funext j
  exact MatrixIso.linearEquiv_congr_symm_apply _ _ _
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
end

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical
variable {R : Type} [CommRing R] {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma linearEquiv_reindex_symm (f : MatrixIso R α β) (a : γ ≃ α) (b : δ ≃ β)
    (x : δ → R) (j : γ) :
    (f.reindex a b).linearEquiv.symm x j=f.linearEquiv.symm (fun i => x (b.symm i)) (a j) :=
  linearEquiv_reindex f.symm b a x j
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma fiberEnum_atom (v : Fin (w.shape.atomicBand.length+1)) (z)
    (c : Option (Secondary n n)) (hc : (w.shape.atomicBand.decoration v).color z=c)
    (hr : (w.shape.vertexAtoms v).rank z=freshRank r w.shape.secondaryRank c)
    (i : Fin ((w.shape.vertexAtoms v).rank z)) :
    ((w.fiberEnum c).symm (finCongr hr i)).val=(w.shape.vertexAtoms v).atom z i := by
  subst c
  change ((Fintype.equivFin _).symm
    ((finCongr (w.shape.card_facetAtoms _)).symm (finCongr hr i))).val=_
  rfl

lemma parentGauge_inverse (v : Fin r → K) (i : Fin r) :
    w.parentGauge.symm v i=w.frame.symm v ((w.fiberEnum none).symm i).val := rfl

lemma rowGauge_apply (i : Fin n) (v : Fin (w.shape.secondaryRank (.row i)) → K) (j : Fin (s i)) :
    w.rowGauge i v (finCongr (w.rowRanks i) j)=
      w.row i.val (fun a => v (w.fiberEnum (some (.row i)) ((w.rowFiberEquiv i).symm a)))
        ⟨⟨i,j⟩,rfl⟩ := by
  change w.row i.val (fun a => v (w.fiberEnum (some (.row i)) ((w.rowFiberEquiv i).symm a)))
    ((sigmaGradeEquiv s i).symm ((finCongr (w.rowRanks i)).symm (finCongr (w.rowRanks i) j)))=_
  rw [Equiv.symm_apply_apply]
  rfl
end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical
variable {R : Type} [CommRing R] {α β : Type} [Fintype α] [Fintype β]
lemma apply_of_reindex (u : MatrixIso R α α) (v : MatrixIso R β β) (e : α ≃ β)
    (h : u.reindex e.symm e.symm=v) (x : α → R) (i : α) :
    u.linearEquiv x i=v.linearEquiv (fun j => x (e.symm j)) (e i) := by
  have hh := congrArg (fun M : MatrixIso R β β =>
    M.linearEquiv (fun j => x (e.symm j)) (e i)) h
  simpa only [linearEquiv_reindex,Equiv.symm_symm,Equiv.symm_apply_apply] using hh
lemma symm_apply_of_reindex (u : MatrixIso R α α) (v : MatrixIso R β β) (e : α ≃ β)
    (h : u.reindex e.symm e.symm=v) (x : α → R) (i : α) :
    u.linearEquiv.symm x i=v.linearEquiv.symm (fun j => x (e.symm j)) (e i) := by
  have hh := congrArg (fun M : MatrixIso R β β =>
    M.linearEquiv.symm (fun j => x (e.symm j)) (e i)) h
  simpa only [linearEquiv_reindex_symm,Equiv.symm_symm,Equiv.symm_apply_apply] using hh
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)
lemma first_parent_inverse (v : Fin r → K)
    (j : Fin ((w.shape.vertexAtoms 0).rank ⟨(w.shape.atomicBand.kind 0).input,none⟩)) :
    ((w.vertexBases 0).basis (w.shape.atomicBand.kind 0).input none).linearEquiv.symm
      (fun j => v (finCongr w.firstParent_rank j)) j=
      w.frame.symm v ((w.shape.vertexAtoms 0).atom ⟨(w.shape.atomicBand.kind 0).input,none⟩ j) := by
  erw [MatrixIso.symm_apply_of_reindex _ _ (finCongr w.firstParent_rank)
    (w.basis_at_color 0 _ none none w.shape.atomicBand.input_parent w.firstParent_rank)]
  simp only [Equiv.apply_symm_apply,colorGauge]
  erw [MatrixIso.linearEquiv_ofLinearEquiv]
  change w.parentGauge.symm v (finCongr w.firstParent_rank j)=_
  rw [w.parentGauge_inverse]
  exact congrArg (w.frame.symm v)
    (w.fiberEnum_atom 0 _ none w.shape.atomicBand.input_parent w.firstParent_rank j)

lemma first_frame_inverse (v : Fin r → K)
    (c : (w.shape.atomicBand.kind 0).table.Child (w.shape.atomicBand.kind 0).input)
    (i : Fin ((w.shape.vertexAtoms 0).rank ⟨(w.shape.atomicBand.kind 0).input,some c⟩)) :
    w.firstFrame.symm v (w.firstColumns ⟨c,i⟩)=
      w.row (w.firstChild c).val
        (fun a => w.frame.symm v a.val)
        ⟨w.firstColumns ⟨c,i⟩,rfl⟩ := by
  change ((w.vertexFrames 0 _).reindex _ _).linearEquiv.symm v _=_
  erw [MatrixIso.linearEquiv_reindex_symm,Equiv.symm_apply_apply]
  change ((w.vertexBases 0).reframe (w.shape.vertexAtoms 0).frame _).linearEquiv.symm _ ⟨c,i⟩=_
  erw [AtomicData.reframe_inverse]
  have hin (j) := w.first_parent_inverse v ((w.shape.vertexAtoms 0).portEquiv _ ⟨c,j⟩)
  have hf : (fun j => ((w.vertexBases 0).basis (w.shape.atomicBand.kind 0).input none).linearEquiv.symm
    (fun j => v (finCongr w.firstParent_rank j)) ((w.shape.vertexAtoms 0).portEquiv _ ⟨c,j⟩))=
    (fun j => w.frame.symm v ((w.shape.vertexAtoms 0).atom ⟨(w.shape.atomicBand.kind 0).input,some c⟩ j)) := by
    funext j
    exact (hin j).trans (congrArg (w.frame.symm v) ((w.shape.vertexAtoms 0).atom_port _ ⟨c,j⟩))
  erw [hf]
  erw [MatrixIso.apply_of_reindex _ _ (finCongr
    ((w.shape.vertexAtoms_rank 0 _).trans (congrArg (freshRank r w.shape.secondaryRank)
      (w.firstChild_color c))))
    (w.basis_at_color 0 _ (some c) (some (.row (w.firstChild c))) (w.firstChild_color c) _)]
  change (MatrixIso.ofLinearEquiv (w.rowGauge (w.firstChild c))).linearEquiv _ _=_
  erw [MatrixIso.linearEquiv_ofLinearEquiv]
  rw [show (finCongr ((w.shape.vertexAtoms_rank 0 _).trans
      (congrArg (freshRank r w.shape.secondaryRank) (w.firstChild_color c))) i)=
    finCongr (w.rowRanks (w.firstChild c)) (finCongr (w.firstChild_rank c) i) from rfl]
  erw [w.rowGauge_apply]
  apply congrArg (fun z => w.row (w.firstChild c).val z ⟨w.firstColumns ⟨c,i⟩,rfl⟩)
  funext a
  apply congrArg (w.frame.symm v)
  have hh := w.fiberEnum_atom 0 ⟨(w.shape.atomicBand.kind 0).input,some c⟩
    (some (.row (w.firstChild c))) (w.firstChild_color c)
    ((w.shape.vertexAtoms_rank 0 _).trans (congrArg (freshRank r w.shape.secondaryRank)
      (w.firstChild_color c)))
    ((finCongr ((w.shape.vertexAtoms_rank 0 _).trans (congrArg (freshRank r w.shape.secondaryRank)
      (w.firstChild_color c)))).symm
        (w.fiberEnum (some (.row (w.firstChild c))) ((w.rowFiberEquiv (w.firstChild c)).symm a)))
  simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply] at hh
  exact hh.symm

lemma firstFrame_eq : w.firstFrame=
    (sumGrades (rowGrade w.shape) (fun i : (i : Fin n) × Fin (s i) => i.1.val) w.row).symm.trans w.frame := by
  have he : w.firstFrame.symm=
      ((sumGrades (rowGrade w.shape) (fun i : (i : Fin n) × Fin (s i) => i.1.val) w.row).symm.trans w.frame).symm := by
    ext v j
    obtain ⟨⟨c,i⟩,rfl⟩ := w.firstColumns.surjective j
    exact w.first_frame_inverse v c i
  exact congrArg LinearEquiv.symm he

/-- The first gallery frame preserves the named quotient maps of the original frame. -/
theorem firstFrame_holds : SameFramedFlag (fun i : (i : Fin n) × Fin (s i) => i.1.val)
    w.firstFrame f := by
  rw [w.firstFrame_eq]
  exact namedFrame_holds _ _ w.frame f w.row w.rowPrefix w.rowNamed

end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)
lemma lastArity : (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).arity (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output=n := by
  have hh := congrArg List.length w.shape.atomicBand.output_children
  simpa only [Decoration.children_length,List.length_map,List.length_ofFn] using hh

def lastChild : (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).table.Child (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output ≃ Fin n :=
  ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).childEnumeration _).trans (finCongr w.lastArity)

lemma lastChild_color (c) : (w.shape.atomicBand.decoration (Fin.last w.shape.atomicBand.length)).color
    ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,some c⟩=some (.col (w.lastChild c)) := by
  let i := ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).childEnumeration _ c)
  have hh := congrArg (fun l : List (Option (Secondary n n)) => l[i.val]?)
    w.shape.atomicBand.output_children
  have hi : i.val<n := i.isLt.trans_eq w.lastArity
  simp only [Decoration.children,List.map_ofFn,List.getElem?_ofFn,dite_eq_left i.isLt,dite_eq_left hi] at hh
  exact (Decoration.portColor_child _ _ c).symm.trans (Option.some.inj hh)

lemma lastParent_rank : (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).rank ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,none⟩=r := by
  exact (w.shape.vertexAtoms_rank (Fin.last w.shape.atomicBand.length) _).trans
    (congrArg (freshRank r w.shape.secondaryRank) w.shape.atomicBand.output_parent)

lemma lastChild_rank (c) : (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).rank
    ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,some c⟩=s (w.lastChild c) :=
  (w.shape.vertexAtoms_rank (Fin.last w.shape.atomicBand.length) _).trans
    ((congrArg (freshRank r w.shape.secondaryRank) (w.lastChild_color c)).trans
      (w.colRanks (w.lastChild c)).symm)

def lastColumns : (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).localRanks.Columns (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output ≃
    ((i : Fin n) × Fin (s i)) :=
  Equiv.sigmaCongr w.lastChild (fun c => finCongr (w.lastChild_rank c))

def lastFrame : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K) :=
  ((w.vertexFrames (Fin.last w.shape.atomicBand.length) (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output).reindex
    w.lastColumns.symm (finCongr w.lastParent_rank).symm).linearEquiv

lemma colGauge_apply (i : Fin n) (v : Fin (w.shape.secondaryRank (.col i)) → K) (j : Fin (s i)) :
    w.colGauge i v (finCongr (w.colRanks i) j)=
      w.col i.val (fun a => v (w.fiberEnum (some (.col i)) ((w.colFiberEquiv i).symm a)))
        ⟨⟨i,j⟩,rfl⟩ := by
  change w.col i.val (fun a => v (w.fiberEnum (some (.col i)) ((w.colFiberEquiv i).symm a)))
    ((sigmaGradeEquiv s i).symm ((finCongr (w.colRanks i)).symm (finCongr (w.colRanks i) j)))=_
  rw [Equiv.symm_apply_apply]
  rfl
end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)
lemma last_parent_inverse (v : Fin r → K)
    (j : Fin ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).rank ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,none⟩)) :
    ((w.vertexBases (Fin.last w.shape.atomicBand.length)).basis (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output none).linearEquiv.symm
      (fun j => v (finCongr w.lastParent_rank j)) j=
      w.frame.symm v ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).atom ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,none⟩ j) := by
  erw [MatrixIso.symm_apply_of_reindex _ _ (finCongr w.lastParent_rank)
    (w.basis_at_color (Fin.last w.shape.atomicBand.length) _ none none w.shape.atomicBand.output_parent w.lastParent_rank)]
  simp only [Equiv.apply_symm_apply,colorGauge]
  erw [MatrixIso.linearEquiv_ofLinearEquiv]
  change w.parentGauge.symm v (finCongr w.lastParent_rank j)=_
  rw [w.parentGauge_inverse]
  exact congrArg (w.frame.symm v)
    (w.fiberEnum_atom (Fin.last w.shape.atomicBand.length) _ none w.shape.atomicBand.output_parent w.lastParent_rank j)

lemma last_frame_inverse (v : Fin r → K)
    (c : (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).table.Child (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output)
    (i : Fin ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).rank ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,some c⟩)) :
    w.lastFrame.symm v (w.lastColumns ⟨c,i⟩)=
      w.col (w.lastChild c).val
        (fun a => w.frame.symm v a.val)
        ⟨w.lastColumns ⟨c,i⟩,rfl⟩ := by
  change ((w.vertexFrames (Fin.last w.shape.atomicBand.length) _).reindex _ _).linearEquiv.symm v _=_
  erw [MatrixIso.linearEquiv_reindex_symm,Equiv.symm_apply_apply]
  change ((w.vertexBases (Fin.last w.shape.atomicBand.length)).reframe (w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).frame _).linearEquiv.symm _ ⟨c,i⟩=_
  erw [AtomicData.reframe_inverse]
  have hin (j) := w.last_parent_inverse v ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).portEquiv _ ⟨c,j⟩)
  have hf : (fun j => ((w.vertexBases (Fin.last w.shape.atomicBand.length)).basis (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output none).linearEquiv.symm
    (fun j => v (finCongr w.lastParent_rank j)) ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).portEquiv _ ⟨c,j⟩))=
    (fun j => w.frame.symm v ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).atom ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,some c⟩ j)) := by
    funext j
    exact (hin j).trans (congrArg (w.frame.symm v) ((w.shape.vertexAtoms (Fin.last w.shape.atomicBand.length)).atom_port _ ⟨c,j⟩))
  erw [hf]
  erw [MatrixIso.apply_of_reindex _ _ (finCongr
    ((w.shape.vertexAtoms_rank (Fin.last w.shape.atomicBand.length) _).trans (congrArg (freshRank r w.shape.secondaryRank)
      (w.lastChild_color c))))
    (w.basis_at_color (Fin.last w.shape.atomicBand.length) _ (some c) (some (.col (w.lastChild c))) (w.lastChild_color c) _)]
  change (MatrixIso.ofLinearEquiv (w.colGauge (w.lastChild c))).linearEquiv _ _=_
  erw [MatrixIso.linearEquiv_ofLinearEquiv]
  rw [show (finCongr ((w.shape.vertexAtoms_rank (Fin.last w.shape.atomicBand.length) _).trans
      (congrArg (freshRank r w.shape.secondaryRank) (w.lastChild_color c))) i)=
    finCongr (w.colRanks (w.lastChild c)) (finCongr (w.lastChild_rank c) i) from rfl]
  erw [w.colGauge_apply]
  apply congrArg (fun z => w.col (w.lastChild c).val z ⟨w.lastColumns ⟨c,i⟩,rfl⟩)
  funext a
  apply congrArg (w.frame.symm v)
  have hh := w.fiberEnum_atom (Fin.last w.shape.atomicBand.length) ⟨(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output,some c⟩
    (some (.col (w.lastChild c))) (w.lastChild_color c)
    ((w.shape.vertexAtoms_rank (Fin.last w.shape.atomicBand.length) _).trans (congrArg (freshRank r w.shape.secondaryRank)
      (w.lastChild_color c)))
    ((finCongr ((w.shape.vertexAtoms_rank (Fin.last w.shape.atomicBand.length) _).trans (congrArg (freshRank r w.shape.secondaryRank)
      (w.lastChild_color c)))).symm
        (w.fiberEnum (some (.col (w.lastChild c))) ((w.colFiberEquiv (w.lastChild c)).symm a)))
  simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply] at hh
  exact hh.symm

lemma lastFrame_eq : w.lastFrame=
    (sumGrades (colGrade w.shape) (fun i : (i : Fin n) × Fin (s i) => i.1.val) w.col).symm.trans w.frame := by
  have he : w.lastFrame.symm=
      ((sumGrades (colGrade w.shape) (fun i : (i : Fin n) × Fin (s i) => i.1.val) w.col).symm.trans w.frame).symm := by
    ext v j
    obtain ⟨⟨c,i⟩,rfl⟩ := w.lastColumns.surjective j
    exact w.last_frame_inverse v c i
  exact congrArg LinearEquiv.symm he

/-- The last gallery frame preserves the named quotient maps of the original frame. -/
theorem lastFrame_holds : SameFramedFlag (fun i : (i : Fin n) × Fin (s i) => i.1.val)
    w.lastFrame h := by
  rw [w.lastFrame_eq]
  exact namedFrame_holds _ _ w.frame h w.col w.colPrefix w.colNamed

end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

end OAI
