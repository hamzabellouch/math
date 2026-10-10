import OAI.AlgebraicGeometry.CharacterVarieties.Frames.AtomicFlags
import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.Grafting
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.VertexGauge

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {α β : Type*} [Fintype α] [Fintype β]
def ofLinearEquiv (e : (α → R) ≃ₗ[R] (β → R)) : MatrixIso R α β where
  val := LinearMap.toMatrix' e.toLinearMap
  inv := LinearMap.toMatrix' e.symm.toLinearMap
  val_inv := by
    rw [←LinearMap.toMatrix'_comp]
    simp
  inv_val := by
    rw [←LinearMap.toMatrix'_comp]
    simp
@[simp] lemma linearEquiv_ofLinearEquiv (e : (α → R) ≃ₗ[R] (β → R)) :
    (ofLinearEquiv e).linearEquiv=e := by
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.toMatrix'.symm_apply_apply _
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {A : Type*} {k : Kind}
namespace AtomicData
variable (D : AtomicData k A)
def mirror : AtomicData k.mirror A where
  atoms z := D.atoms (k.mirrorEnd.symm z)
  corner z := by
    have h := k.mirror_mate (k.mirrorEnd.symm z)
    rw [k.mirrorEnd.apply_symm_apply] at h
    rw [←h,k.mirrorEnd.symm_apply_apply]
    exact D.corner _
  child_subset p c := by
    obtain ⟨p,rfl⟩ := k.mirrorPort.surjective p
    obtain ⟨c,rfl⟩ := (k.mirrorChild p).surjective c
    change D.atoms (k.mirrorEnd.symm (k.mirrorEnd ⟨p,some c⟩)) ⊆
      D.atoms (k.mirrorEnd.symm (k.mirrorEnd ⟨p,none⟩))
    simp only [Equiv.symm_apply_apply]
    exact D.child_subset p c
  partition p t ht := by
    obtain ⟨p,rfl⟩ := k.mirrorPort.surjective p
    change t∈D.atoms (k.mirrorEnd.symm (k.mirrorEnd ⟨p,none⟩)) at ht
    rw [Equiv.symm_apply_apply] at ht
    obtain ⟨c,hc,hu⟩ := D.partition p t ht
    refine ⟨k.mirrorChild p c,?_,?_⟩
    · change t∈D.atoms (k.mirrorEnd.symm (k.mirrorEnd ⟨p,some c⟩))
      rwa [Equiv.symm_apply_apply]
    · intro c' hc'
      obtain ⟨c',rfl⟩ := (k.mirrorChild p).surjective c'
      change t∈D.atoms (k.mirrorEnd.symm (k.mirrorEnd ⟨p,some c'⟩)) at hc'
      rw [Equiv.symm_apply_apply] at hc'
      exact congrArg (k.mirrorChild p) (hu c' hc')
@[simp] lemma mirror_atoms (z) : D.mirror.atoms (k.mirrorEnd z)=D.atoms z := by
  simp only [mirror,Equiv.symm_apply_apply]
end AtomicData
namespace LocalRanks
@[ext] lemma ext_rank {d e : LocalRanks k} (h : d.rank=e.rank) : d=e := by
  cases d; cases e; cases h; rfl
end LocalRanks
namespace AtomicData
variable [Fintype A] (D : AtomicData k A) (d : LocalRanks k)
    (h : ∀ p c,D.rank ⟨p,c⟩=d.rank p c)
include h in
lemma ranks_eq : D.localRanks=d := LocalRanks.ext_rank (funext fun p => funext (h p))
def framesAtRanks {R : Type*} [CommRing R] :
    (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p) :=
  D.ranks_eq d h ▸ D.frame
lemma framesAtRanks_holds {R : Type*} [CommRing R] :
    (LocalRanks.comparison k d (D.framesAtRanks d h (R:=R))).Holds := by
  have he := D.ranks_eq d h
  subst d
  exact D.comparison_holds

end AtomicData
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
open TwoFlagBand
variable {K : Type} [Field K]

def sigmaGradeEquiv {n : ℕ} (s : Fin n → ℕ) (i : Fin n) :
    {a : (j : Fin n) × Fin (s j) // a.1.val=i.val} ≃ Fin (s i) where
  toFun a := (finCongr (congrArg s (Fin.ext a.property))) a.val.2
  invFun j := ⟨⟨i,j⟩,rfl⟩
  left_inv a := by
    rcases a with ⟨⟨j,x⟩,h⟩
    obtain rfl : j=i := Fin.ext h
    rfl
  right_inv _ := rfl

lemma rowGrade_card {n m r : ℕ} (d : RankShape n m r) (i : Fin n) :
    Fintype.card {a // rowGrade d a=i.val}=d.secondaryRank (.row i) := by
  let e : {a // rowGrade d a=i.val} ≃ {a : d.Atom // a∈d.secondaryAtoms (.row i)} :=
    Equiv.subtypeEquivRight fun a => (Fin.ext_iff).symm
  exact (Fintype.card_congr e).trans (d.card_secondaryAtoms (.row i))

lemma colGrade_card {n m r : ℕ} (d : RankShape n m r) (i : Fin m) :
    Fintype.card {a // colGrade d a=i.val}=d.secondaryRank (.col i) := by
  let e : {a // colGrade d a=i.val} ≃ {a : d.Atom // a∈d.secondaryAtoms (.col i)} :=
    Equiv.subtypeEquivRight fun a => (Fin.ext_iff).symm
  exact (Fintype.card_congr e).trans (d.card_secondaryAtoms (.col i))

lemma row_rank {n m r : ℕ} (d : RankShape n m r) (s : Fin n → ℕ)
    (row : (k : ℕ) → ({a // rowGrade d a=k} → K) ≃ₗ[K]
      ({a : (j : Fin n) × Fin (s j) // a.1.val=k} → K)) (i : Fin n) :
    s i=d.secondaryRank (.row i) := by
  have h := (row i.val).finrank_eq
  simp only [Module.finrank_pi] at h
  simpa only [Fintype.card_fin] using ((Fintype.card_congr (sigmaGradeEquiv s i)).symm.trans h.symm).trans (rowGrade_card d i)

lemma col_rank {n m r : ℕ} (d : RankShape n m r) (s : Fin m → ℕ)
    (col : (k : ℕ) → ({a // colGrade d a=k} → K) ≃ₗ[K]
      ({a : (j : Fin m) × Fin (s j) // a.1.val=k} → K)) (i : Fin m) :
    s i=d.secondaryRank (.col i) := by
  have h := (col i.val).finrank_eq
  simp only [Module.finrank_pi] at h
  simpa only [Fintype.card_fin] using ((Fintype.card_congr (sigmaGradeEquiv s i)).symm.trans h.symm).trans (colGrade_card d i)
end IntegralCharacterVarieties.NamedBandGrades
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
open TwoFlagBand
variable {K : Type} [Field K] {n r : ℕ} (s : Fin n → ℕ)
/-- A named simultaneous splitting of two frames. -/
structure IdentifiedBand
    (f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)) where
  shape : RankShape n n r
  frame : (Atoms shape → K) ≃ₗ[K] (Fin r → K)
  row : (k : ℕ) → ({a // rowGrade shape a=k} → K) ≃ₗ[K]
      ({a : (i : Fin n) × Fin (s i) // a.1.val=k} → K)
  col : (k : ℕ) → ({a // colGrade shape a=k} → K) ≃ₗ[K]
      ({a : (i : Fin n) × Fin (s i) // a.1.val=k} → K)
  rowPrefix : ∀ k,framedPrefix (rowGrade shape) frame k=framedPrefix (fun i => i.1.val) f k
  colPrefix : ∀ k,framedPrefix (colGrade shape) frame k=framedPrefix (fun i => i.1.val) h k
  rowNamed : ∀ k v,v∈framedPrefix (rowGrade shape) frame (k+1) →
    row k (framedGrade (rowGrade shape) frame k v)=framedGrade (fun i => i.1.val) f k v
  colNamed : ∀ k v,v∈framedPrefix (colGrade shape) frame (k+1) →
    col k (framedGrade (colGrade shape) frame k v)=framedGrade (fun i => i.1.val) h k v

variable {s}
lemma identifiedBand_nonempty
    (f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)) :
    Nonempty (IdentifiedBand s f h) := by
  have w := actual_named_band_grades (fun i : (i : Fin n) × Fin (s i) => i.1)
    (fun i : (i : Fin n) × Fin (s i) => i.1) f h
  have hd : Module.finrank K (Fin r → K)=r := by simp
  rw [hd] at w
  obtain ⟨d,e,row,col,hr,hc,hnr,hnc⟩ := w
  exact ⟨⟨d,e,row,col,hr,hc,hnr,hnc⟩⟩

def identifiedBand
    (f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)) :
    IdentifiedBand s f h := Classical.choice (identifiedBand_nonempty f h)

namespace IdentifiedBand
variable {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)
lemma rowRanks (i : Fin n) : s i=w.shape.secondaryRank (.row i) := row_rank w.shape s w.row i
lemma colRanks (i : Fin n) : s i=w.shape.secondaryRank (.col i) := col_rank w.shape s w.col i
end IdentifiedBand
end IntegralCharacterVarieties.NamedBandGrades
end
noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open MatrixExpression NamedBandGrades OccurrenceIncidence
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S)

def namedSeamFrame (u : (Matrix (Fin (D.seamDim q)) (Fin (D.seamDim q)) K)ˣ) :
    (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K) :=
  ((MatrixIso.unit u).reindex (blockIndex (D.childDim q)).symm (finCongr (D.seamRank q))).linearEquiv

def bandFromOldFrames (f h : (Matrix (Fin (D.seamDim q)) (Fin (D.seamDim q)) K)ˣ) :
    IdentifiedBand (D.childDim q) (D.namedSeamFrame q f) (D.namedSeamFrame q h) :=
  identifiedBand _ _

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical
variable {R F : Type} [CommRing R] {k : Kind} (d : LocalRanks k)
    (c : Decoration k F) (rank : F → ℕ)
    (hr : ∀ p a,d.rank p a=rank (c.color ⟨p,a⟩))
    (G : (f : F) → MatrixIso R (Fin (rank f)) (Fin (rank f)))
private lemma colorBases_aux {R F : Type} [CommRing R] (rank : F → ℕ)
    (G : (f : F) → MatrixIso R (Fin (rank f)) (Fin (rank f)))
    {c e : F} (hf : c=e) {n m : ℕ} (hc : n=rank c) (he : m=rank e) (hn : m=n) :
    ((G c).reindex (finCongr hc) (finCongr hc)).reindex (finCongr hn) (finCongr hn)=
      (G e).reindex (finCongr he) (finCongr he) := by
  subst e
  subst n
  subst m
  rfl

/-- Bases on named secondary labels satisfy corner coherence at every allowed vertex. -/
def colorBases : d.CoherentBases (R:=R) where
  basis p a := (G (c.color ⟨p,a⟩)).reindex (finCongr (hr p a)) (finCongr (hr p a))
  corner z := colorBases_aux rank G (c.corner z)
    (hr (k.table.mate z).1 (k.table.mate z).2) (hr z.1 z.2) (d.corner z).symm
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
end

end OAI
