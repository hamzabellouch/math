import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.RoutedFamilies

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch
open scoped Classical
open VertexTable


/-- The rank identities on all three ports of every split/merge and on both ports of both interchanges. There is no unverified seam-rank premise. -/
theorem rank_sum (a b h x y : ℕ) (v : Vertex) (p : (kind v).table.Port) :
    rank a b h x y ((decoration v).color ⟨p,none⟩)=
      ∑ j, rank a b h x y ((decoration v).color ⟨p,some j⟩) := by
  rw [← @Equiv.sum_comp _ _ _ (Fin.fintype _) (fintypeChild (kind v) p) _
    ((kind v).childEnumeration p).symm]
  cases v <;> cases p <;>
    first | erw [Fin.sum_univ_two] | erw [Fin.sum_univ_three]
  all_goals first
    | rfl
    | change a+b+h=a+(b+h)
    | change a+b+h=(b+a)+h
    | change a+b+h=b+(a+h)
    | change a+h+x=a+(h+x)
    | change h+x+y=(h+y)+x
    | change b+h+y=b+(h+y)
  all_goals omega

def vertexRanks (a b h x y : ℕ) (v : Vertex) : LocalRanks (kind v) where
  rank p c := rank a b h x y ((decoration v).color ⟨p,c⟩)
  corner z := congrArg (rank a b h x y) ((decoration v).corner z)
  sum p := rank_sum a b h x y v p

/-- All auxiliary strips/disks are at most one of A,B. Thus the patch lowers rank whenever the four replaced parents are already below the original n. -/
theorem rank_strict {a b h x y n : ℕ}
    (hU : a+b+h<n) (hQ : h+x+y<n) (hA : a+h+x<n) (hB : b+h+y<n) (f : Facet) :
    rank a b h x y f<n := by
  cases f <;> dsimp [rank] <;> omega

/-- Finite numerical choices for the local replacement. In a global family every vertex uses an independent occurrence of this bounded array. -/
def RankArray (n : ℕ) :=
  {z : Fin 5 → Fin (n+1) // (z 0).val + (z 1).val + (z 2).val < n ∧ (z 2).val + (z 3).val + (z 4).val < n ∧
    (z 0).val + (z 2).val + (z 3).val < n ∧ (z 1).val + (z 2).val + (z 4).val < n}

instance (n : ℕ) : Finite (RankArray n) := by unfold RankArray; infer_instance

end IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[simp] lemma congr_trans (e : α ≃ β) (f : β ≃ γ) :
    (congr (R:=R) e).trans (congr f) = congr (e.trans f) := by
  apply ext <;> ext i j <;>
    simp [congr,reindex,refl,trans,Matrix.one_apply,
      Equiv.eq_symm_apply,eq_comm]

@[simp] lemma congr_reindex {δ ε : Type*} [Fintype δ] [Fintype ε]
    (e : α ≃ β) (f : δ ≃ α) (g : ε ≃ β) :
    (congr (R:=R) e).reindex f g = congr (f.trans (e.trans g.symm)) := by
  apply ext <;> ext i j <;>
    simp [congr,reindex,refl,Matrix.one_apply,Equiv.eq_symm_apply,
      eq_comm]

@[simp] lemma congr_sum {α' β' : Type*} [Fintype α'] [Fintype β']
    (e : α ≃ β) (f : α' ≃ β') :
    (congr (R:=R) e).sum (congr f) = congr (Equiv.sumCongr e f) := by
  apply ext <;> ext i j <;> cases i <;> cases j <;>
    simp [congr,reindex,refl,sum,Matrix.fromBlocks,Matrix.one_apply]

lemma holds_self {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → ℕ) (f : MatrixIso R ι κ) :
    SameFramedFlag g f.linearEquiv f.linearEquiv := by
  rw [sameFramedFlag_iff]
  simp only [f.inv_val]
  intros; trivial
end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R]

section Passage
variable {m : ℕ} {t : Passage m} (d : LocalRanks (.passage m t))
local instance : Fintype (d.Columns false) := d.fintypeColumns false
local instance : Fintype (d.Columns true) := d.fintypeColumns true
lemma passageComparison_congr
    (e : ∀ p, d.Columns p ≃ d.Parent p)
    (h : e false = d.passageColumns.trans ((e true).trans d.passageParent.symm)) :
    let c := d.passageComparison (fun p => MatrixIso.congr (R:=R) (e p))
    c.left=c.right := by
  change MatrixIso.congr (e false) =
    (MatrixIso.congr (e true)).reindex d.passageColumns d.passageParent
  rw [MatrixIso.congr_reindex, h]

end Passage
section Split
variable {a b c : ℕ} (d : LocalRanks (.splitting a b c false))
local instance : Fintype (d.Columns .before) := d.fintypeColumns .before
local instance : Fintype (d.Columns .after) := d.fintypeColumns .after
local instance : Fintype (d.Columns .branch) := d.fintypeColumns .branch
def splitRefinementEquiv
    (e : d.Columns .branch ≃ d.Parent .branch) :
    d.Columns .after ≃ d.Columns .before :=
  d.splitAfter.trans ((Equiv.sumCongr d.splitPrefix
    (Equiv.sumCongr (d.splitBranchChildren.trans (e.trans d.splitBranchParent.symm))
      d.splitSuffix)).trans d.splitBefore.symm)

lemma splitRefinement_congr
    (e : d.Columns .branch ≃ d.Parent .branch) :
    d.splitRefinement (MatrixIso.congr (R:=R) e) =
      MatrixIso.congr (d.splitRefinementEquiv e) := by
  simp only [splitRefinement, MatrixIso.congr_reindex, MatrixIso.congr_sum,
    splitRefinementEquiv]

lemma splitComparison_congr
    (e : ∀ p, d.Columns p ≃ d.Parent p)
    (h : e .after = (d.splitRefinementEquiv (e .branch)).trans
      ((e .before).trans d.splitParent.symm)) :
    let c := d.splitComparison (fun p => MatrixIso.congr (R:=R) (e p))
    c.left=c.right := by
  change MatrixIso.congr (e .after) =
    ((d.splitRefinement (MatrixIso.congr (e .branch))).trans
      (MatrixIso.congr (e .before))).reindex (Equiv.refl _) d.splitParent
  rw [splitRefinement_congr, MatrixIso.congr_trans, MatrixIso.congr_reindex, h]
  congr 1
end Split
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[simp] lemma trans_assoc (x : MatrixIso R α β) (y : MatrixIso R β γ)
    {δ : Type*} [Fintype δ] (z : MatrixIso R γ δ) :
    (x.trans y).trans z=x.trans (y.trans z) := by
  apply ext <;> simp only [trans,Matrix.mul_assoc]

lemma reindex_trans {α' β' γ' : Type*} [Fintype α'] [Fintype β'] [Fintype γ']
    (x : MatrixIso R α β) (y : MatrixIso R β γ)
    (a : α' ≃ α) (b : β' ≃ β) (c : γ' ≃ γ) :
    (x.trans y).reindex a c=(x.reindex a b).trans (y.reindex b c) := by
  apply ext <;> simp only [trans,reindex,Matrix.submatrix_mul_equiv]

@[simp] lemma reindex_refl_eq (x : MatrixIso R α β) :
    x.reindex (Equiv.refl _) (Equiv.refl _)=x := by cases x; rfl

/-- Unit-valued diagonal, valid over the full coefficient ring. -/
def diagonal (u : α → Rˣ) : MatrixIso R α α where
  val := Matrix.diagonal (fun i => (u i : R))
  inv := Matrix.diagonal (fun i => ((u i)⁻¹ : Rˣ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.mul_inv]
    exact Matrix.diagonal_one
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.inv_mul]
    exact Matrix.diagonal_one

lemma diagonal_naturality (e : α ≃ β) (u : β → Rˣ) :
    (congr (R:=R) e).trans (diagonal u)=
      (diagonal (u ∘ e)).trans (congr e) := by
  apply ext <;> ext i j <;>
    simp [trans,diagonal,congr,reindex,refl,Matrix.one_apply,
      Matrix.diagonal_mul,Matrix.mul_diagonal,
      eq_comm] <;> split_ifs with h <;> simp_all

end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {a b c : ℕ} (d : LocalRanks (.splitting a b c false))
local instance : Fintype (d.Columns .before) := d.fintypeColumns .before
local instance : Fintype (d.Columns .after) := d.fintypeColumns .after
local instance : Fintype (d.Columns .branch) := d.fintypeColumns .branch

/-- Change the common parent frame, keeping the named third-seam frame. -/
def changeSplitParent (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p))
    (z : MatrixIso R (d.Parent .before) (d.Parent .before)) :
    ∀ p, MatrixIso R (d.Columns p) (d.Parent p)
  | .before => (f .before).trans z
  | .after => (f .after).trans (z.reindex d.splitParent d.splitParent)
  | .branch => f .branch

lemma changeSplitParent_comparison_eq
    (f : ∀ p, MatrixIso R (d.Columns p) (d.Parent p))
    (z : MatrixIso R (d.Parent .before) (d.Parent .before))
    (h : (d.splitComparison f).left=(d.splitComparison f).right) :
    (d.splitComparison (d.changeSplitParent f z)).left=
      (d.splitComparison (d.changeSplitParent f z)).right := by
  change (f .after).trans (z.reindex d.splitParent d.splitParent)=
    ((d.splitRefinement (f .branch)).trans ((f .before).trans z)).reindex
      (Equiv.refl _) d.splitParent
  rw [← MatrixIso.trans_assoc]
  rw [MatrixIso.reindex_trans _ z (Equiv.refl _) d.splitParent d.splitParent]
  exact congrArg (fun w => w.trans (z.reindex d.splitParent d.splitParent)) h

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
namespace IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch
open scoped Classical Matrix
open VertexTable

/-- The five genuinely named small fibers in the manuscript normal form. These are names, not extra geometric constraints on an old subspace. -/
def atoms : Facet → Finset (Fin 5)
  | .U => {0,1,2} | .Q => {2,3,4} | .A => {0,2,3} | .B => {1,2,4}
  | .TB => {1,2} | .HX => {2,3} | .TA => {0,2} | .HY => {2,4}
  | .a => {0} | .b => {1} | .h => {2} | .x => {3} | .y => {4}

def Fiber (r : Fin 5 → ℕ) (f : Facet) :=
  {i : (t : Fin 5) × Fin (r t) // i.1 ∈ atoms f}
instance (r : Fin 5 → ℕ) (f : Facet) : Fintype (Fiber r f) :=
  inferInstanceAs (Fintype {i : (t : Fin 5) × Fin (r t) // i.1 ∈ atoms f})

def fiberSigma (r : Fin 5 → ℕ) (f : Facet) :
    Fiber r f ≃ ((t : {t : Fin 5 // t∈atoms f}) × Fin (r t)) where
  toFun i := ⟨⟨i.val.1,i.property⟩,i.val.2⟩
  invFun i := ⟨⟨i.1.val,i.2⟩,i.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_fiber (r : Fin 5 → ℕ) (f : Facet) :
    Fintype.card (Fiber r f)=rank (r 0) (r 1) (r 2) (r 3) (r 4) f := by
  rw [Fintype.card_congr (fiberSigma r f), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_coe_sort]
  cases f <;> simp [atoms,rank,Finset.sum_insert,add_assoc]

def fiberEnum (r : Fin 5 → ℕ) (f : Facet) :
    Fiber r f ≃ Fin (rank (r 0) (r 1) (r 2) (r 3) (r 4) f) :=
  (Fintype.equivFin _).trans (finCongr (card_fiber r f))

/-- Every ordered port partitions the named atom coordinates. The assertion is verified for the ten-vertex table. -/
lemma atom_partition (v : Vertex) (p : (kind v).table.Port) (t : Fin 5) :
    (∃! c, t ∈ atoms ((decoration v).color ⟨p,some c⟩)) ↔
      t ∈ atoms ((decoration v).color ⟨p,none⟩) := by
  rw [((kind v).childEnumeration p).existsUnique_congr_left]
  cases v <;> cases p <;> fin_cases t <;> simp only [ExistsUnique] <;> decide

lemma child_containment (v : Vertex) (p : (kind v).table.Port)
    (c : (kind v).table.Child p) (t : Fin 5)
    (ht : t ∈ atoms ((decoration v).color ⟨p,some c⟩)) :
    t ∈ atoms ((decoration v).color ⟨p,none⟩) := by
  cases v <;> cases p
  all_goals dsimp only [kind,Kind.table,reverse,split,splitChild,Passage.table,passage] at c
  all_goals fin_cases c <;> fin_cases t <;> (revert ht; decide)

variable (r : Fin 5 → ℕ) (v : Vertex) (p : (kind v).table.Port)

def flattenFun : ((c : (kind v).table.Child p) ×
      Fiber r ((decoration v).color ⟨p,some c⟩)) →
    Fiber r ((decoration v).color ⟨p,none⟩)
  | ⟨c,i⟩ => ⟨i.val,child_containment v p c i.val.1 i.property⟩

lemma flattenFun_bijective : Function.Bijective (flattenFun r v p) := by
  constructor
  · rintro ⟨c,i⟩ ⟨d,j⟩ h
    have hij : i.val=j.val := congrArg Subtype.val h
    have hc := (atom_partition v p i.val.1).mpr
      (child_containment v p c i.val.1 i.property)
    have hcd : c=d := hc.unique i.property (hij.symm ▸ j.property)
    subst d
    have : i=j := Subtype.ext hij
    subst j
    rfl
  · intro i
    obtain ⟨c,hc,hu⟩ := (atom_partition v p i.val.1).mpr i.property
    exact ⟨⟨c,⟨i.val,hc⟩⟩,rfl⟩

def flatten : ((c : (kind v).table.Child p) ×
      Fiber r ((decoration v).color ⟨p,some c⟩)) ≃
    Fiber r ((decoration v).color ⟨p,none⟩) :=
  Equiv.ofBijective _ (flattenFun_bijective r v p)


/-- Ordered seam columns, not an unlabelled flag: first expand each named child into its atoms and then identify with the parent named atoms. -/
def portEquiv : (vertexRanks (r 0) (r 1) (r 2) (r 3) (r 4) v).Columns p ≃
    (vertexRanks (r 0) (r 1) (r 2) (r 3) (r 4) v).Parent p :=
  (Equiv.sigmaCongrRight (fun c =>
    (fiberEnum r ((decoration v).color ⟨p,some c⟩)).symm)).trans
      ((flatten r v p).trans (fiberEnum r ((decoration v).color ⟨p,none⟩)))

variable {R : Type*} [CommRing R]

def positiveFrame : MatrixIso R
    ((vertexRanks (r 0) (r 1) (r 2) (r 3) (r 4) v).Columns p)
    ((vertexRanks (r 0) (r 1) (r 2) (r 3) (r 4) v).Parent p) :=
  MatrixIso.congr (portEquiv r v p)


lemma fiber_enum_cancel {f g : Facet} (x : Fiber r f) (y : Fiber r g)
    (h : x.val=y.val) :
    x.val=((fiberEnum r g).symm ((fiberEnum r g) y)).val := by
  simpa only [Equiv.symm_apply_apply] using h

lemma positive_comparison_eq :
    let c := LocalRanks.comparison (kind v)
      (vertexRanks (r 0) (r 1) (r 2) (r 3) (r 4) v) (positiveFrame (R:=R) r v)
    c.left=c.right := by
  cases v
  case uSwap =>
    apply LocalRanks.passageComparison_congr
      (vertexRanks (r 0) (r 1) (r 2) (r 3) (r 4) .uSwap)
      (portEquiv r .uSwap)
    ext ⟨c,i⟩ : 1
    change Fin 3 at c
    fin_cases c <;> rfl
  case qSwap =>
    apply LocalRanks.passageComparison_congr
      (vertexRanks (r 0) (r 1) (r 2) (r 3) (r 4) .qSwap)
      (portEquiv r .qSwap)
    ext ⟨c,i⟩ : 1
    change Fin 3 at c
    fin_cases c <;> rfl
  all_goals
    apply LocalRanks.splitComparison_congr
    ext ⟨c,i⟩ : 1
    dsimp only [kind,Kind.table,reverse,split,splitChild,
      Passage.table,passage] at c
    fin_cases c <;> first | rfl | skip
  all_goals
    apply congrArg (fiberEnum r _)
    apply Subtype.ext
    first
    | change _ = ((fiberEnum r .TB).symm ((fiberEnum r .TB) _)).val
    | change _ = ((fiberEnum r .HX).symm ((fiberEnum r .HX) _)).val
    | change _ = ((fiberEnum r .TA).symm ((fiberEnum r .TA) _)).val
    | change _ = ((fiberEnum r .HY).symm ((fiberEnum r .HY) _)).val
    apply fiber_enum_cancel
    rfl


end IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch

end

end OAI
