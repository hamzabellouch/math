import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.FreshGallery
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.VertexFrames

namespace OAI

/-!
# Frames from labeled atoms

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical

/-- A literal local decomposition into labeled atoms. It remembers the same
atom across every paired germ and the unique child containing each parent atom.
In applications atoms are the actual simultaneous graded basis vectors, not
just intersection dimensions. -/
structure AtomicData (k : Kind) (A : Type*) where
  atoms : (p : k.table.Port) × Option (k.table.Child p) → Set A
  corner : ∀ z, atoms (k.table.mate z)=atoms z
  child_subset : ∀ p c, atoms ⟨p,some c⟩ ⊆ atoms ⟨p,none⟩
  partition : ∀ p t, t∈atoms ⟨p,none⟩ → ∃! c, t∈atoms ⟨p,some c⟩

namespace AtomicData
variable {k : Kind} {A : Type*} (D : AtomicData k A)
abbrev Fiber (z : (p : k.table.Port) × Option (k.table.Child p)) := {t // t∈D.atoms z}
variable [Fintype A]
def rank (z : (p : k.table.Port) × Option (k.table.Child p)) : ℕ := Fintype.card (D.Fiber z)
def enum (z : (p : k.table.Port) × Option (k.table.Child p)) : D.Fiber z ≃ Fin (D.rank z) :=
  Fintype.equivFin _

end AtomicData
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
end
noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
namespace AtomicData
variable {k : Kind} {A : Type*} (D : AtomicData k A)

lemma child_containment (p : k.table.Port) (c : k.table.Child p) (t : A)
    (h : t∈D.atoms ⟨p,some c⟩) : t∈D.atoms ⟨p,none⟩ := D.child_subset p c h

def flattenFun (p : k.table.Port) :
    ((c : k.table.Child p) × D.Fiber ⟨p,some c⟩) → D.Fiber ⟨p,none⟩
  | ⟨c,i⟩ => ⟨i.val,D.child_subset p c i.property⟩

lemma flattenFun_bijective (p : k.table.Port) : Function.Bijective (D.flattenFun p) := by
  constructor
  · rintro ⟨c,i⟩ ⟨d,j⟩ h
    have hij : i.val=j.val := congrArg Subtype.val h
    have hc := D.partition p i.val (D.child_subset p c i.property)
    have hcd : c=d := hc.unique i.property (hij.symm ▸ j.property)
    subst d
    have : i=j := Subtype.ext hij
    subst j
    rfl
  · intro i
    obtain ⟨c,hc,_⟩ := D.partition p i.val i.property
    exact ⟨⟨c,⟨i.val,hc⟩⟩,rfl⟩

def flatten (p : k.table.Port) :
    ((c : k.table.Child p) × D.Fiber ⟨p,some c⟩) ≃ D.Fiber ⟨p,none⟩ :=
  Equiv.ofBijective _ (D.flattenFun_bijective p)

variable [Fintype A]

lemma sum_rank (p : k.table.Port) : D.rank ⟨p,none⟩ = ∑ c, D.rank ⟨p,some c⟩ := by
  have h := Fintype.card_congr (D.flatten p)
  simpa only [rank,Fintype.card_sigma] using h.symm

def localRanks : LocalRanks k where
  rank p c := D.rank ⟨p,c⟩
  corner z := congrArg (fun s : Set A => Fintype.card {t // t∈s}) (D.corner z)
  sum := D.sum_rank

/-- Literal ordered child basis into the parent's basis, preserving atom names. -/
def portEquiv (p : k.table.Port) : D.localRanks.Columns p ≃ D.localRanks.Parent p :=
  (Equiv.sigmaCongrRight (fun c => (D.enum ⟨p,some c⟩).symm)).trans
    ((D.flatten p).trans (D.enum ⟨p,none⟩))

def atom (z : (p : k.table.Port) × Option (k.table.Child p)) (i : Fin (D.rank z)) : A :=
  ((D.enum z).symm i).val

lemma atom_injective (z : (p : k.table.Port) × Option (k.table.Child p)) :
    Function.Injective (D.atom z) := Subtype.val_injective.comp (D.enum z).symm.injective

lemma atom_port (p : k.table.Port) (i : D.localRanks.Columns p) :
    D.atom ⟨p,none⟩ (D.portEquiv p i)=D.atom ⟨p,some i.1⟩ i.2 := by
  change ((D.enum ⟨p,none⟩).symm ((D.enum ⟨p,none⟩)
    (D.flatten p ⟨i.1,(D.enum ⟨p,some i.1⟩).symm i.2⟩))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma atom_cast {z w : (p : k.table.Port) × Option (k.table.Child p)}
    (h : D.atoms z=D.atoms w) (hr : D.rank z=D.rank w) (i : Fin (D.rank z)) :
    D.atom w (finCongr hr i)=D.atom z i := by
  let aux (s t : Set A) (h : s=t)
      (hr : Fintype.card {a // a∈s}=Fintype.card {a // a∈t})
      (i : Fin (Fintype.card {a // a∈s})) :
      ((Fintype.equivFin {a // a∈t}).symm (finCongr hr i)).val =
        ((Fintype.equivFin {a // a∈s}).symm i).val := by
    subst t
    rfl
  exact aux _ _ h hr i

lemma atom_corner (z : (p : k.table.Port) × Option (k.table.Child p))
    (i : Fin (D.rank z)) :
    D.atom (k.table.mate z) (D.localRanks.cornerEquiv z i)=D.atom z i :=
  D.atom_cast (D.corner z).symm _ i

variable {R : Type*} [CommRing R]
def frame (p : k.table.Port) : MatrixIso R (D.localRanks.Columns p) (D.localRanks.Parent p) :=
  MatrixIso.congr (D.portEquiv p)

end AtomicData
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
end
noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
open scoped Classical Matrix
variable {A : Type*} [Fintype A]
variable {R : Type*} [CommRing R]

section Passage
variable {m : ℕ} {t : Passage m} (D : AtomicData (.passage m t) A)

lemma passage_atom_column (i : D.localRanks.Columns false) :
    D.atom ⟨true,some (D.localRanks.passageColumns i).1⟩ (D.localRanks.passageColumns i).2 =
      D.atom ⟨false,some i.1⟩ i.2 := by
  exact D.atom_corner ⟨false,some i.1⟩ i.2

lemma passage_atom_parent (i : D.localRanks.Parent false) :
    D.atom ⟨true,none⟩ (D.localRanks.passageParent i)=D.atom ⟨false,none⟩ i := by
  exact D.atom_corner ⟨false,none⟩ i

lemma passage_equiv_eq : D.portEquiv false = D.localRanks.passageColumns.trans
    ((D.portEquiv true).trans D.localRanks.passageParent.symm) := by
  ext i : 1
  apply D.atom_injective ⟨false,none⟩
  erw [D.atom_port]
  change _ = D.atom ⟨false,none⟩
    (D.localRanks.passageParent.symm (D.portEquiv true (D.localRanks.passageColumns i)))
  erw [← D.passage_atom_parent,Equiv.apply_symm_apply,D.atom_port,D.passage_atom_column]

lemma passage_comparison_eq :
    let c := LocalRanks.comparison (.passage m t) D.localRanks (D.frame (R:=R))
    c.left=c.right :=
  D.localRanks.passageComparison_congr (D.portEquiv) D.passage_equiv_eq
end Passage

section Split
variable {a b c : ℕ} (D : AtomicData (.splitting a b c false) A)

lemma split_atom_parent (i : D.localRanks.Parent .after) :
    D.atom ⟨.before,none⟩ (D.localRanks.splitParent i)=D.atom ⟨.after,none⟩ i := by
  exact D.atom_corner ⟨.after,none⟩ i

lemma split_refinement_atom (i : D.localRanks.Columns .after) :
    let j := D.localRanks.splitRefinementEquiv (D.portEquiv .branch) i
    D.atom ⟨.before,some j.1⟩ j.2=D.atom ⟨.after,some i.1⟩ i.2 := by
  rcases i with ⟨i,v⟩
  rcases i with i|i|i
  · exact D.atom_corner ⟨.after,some (.inl i)⟩ v
  · change D.atom ⟨.before,some (.inr (.inl ()))⟩
      (D.localRanks.splitBranchParent.symm
        (D.portEquiv .branch (D.localRanks.splitBranchChildren ⟨i,v⟩))) =
      D.atom ⟨.after,some (.inr (.inl i))⟩ v
    have h : ∀ w, D.atom ⟨.branch,none⟩ (D.localRanks.splitBranchParent w)=
        D.atom ⟨.before,some (.inr (.inl ()))⟩ w :=
      fun w => D.atom_corner ⟨.before,some (.inr (.inl ()))⟩ w
    erw [←h,Equiv.apply_symm_apply,D.atom_port]
    exact D.atom_corner ⟨.after,some (.inr (.inl i))⟩ v
  · exact D.atom_corner ⟨.after,some (.inr (.inr i))⟩ v

lemma split_equiv_eq : D.portEquiv .after =
    (D.localRanks.splitRefinementEquiv (D.portEquiv .branch)).trans
      ((D.portEquiv .before).trans D.localRanks.splitParent.symm) := by
  ext i : 1
  apply D.atom_injective ⟨.after,none⟩
  erw [D.atom_port]
  change _ = D.atom ⟨.after,none⟩ (D.localRanks.splitParent.symm
    (D.portEquiv .before (D.localRanks.splitRefinementEquiv (D.portEquiv .branch) i)))
  erw [←D.split_atom_parent,Equiv.apply_symm_apply,D.atom_port]
  exact (D.split_refinement_atom i).symm

lemma split_comparison_eq :
    let z := LocalRanks.comparison (.splitting a b c false) D.localRanks (D.frame (R:=R))
    z.left=z.right :=
  D.localRanks.splitComparison_congr D.portEquiv D.split_equiv_eq
end Split

section Merge
variable {a b c : ℕ} (D : AtomicData (.splitting a b c true) A)
def forward : AtomicData (.splitting a b c false) A where
  atoms := D.atoms
  corner := D.corner
  child_subset := D.child_subset
  partition := D.partition

lemma merge_comparison_eq :
    let z := LocalRanks.comparison (.splitting a b c true) D.localRanks (D.frame (R:=R))
    z.left=z.right := D.forward.split_comparison_eq
end Merge

/-- All actual allowed-vertex frames are induced by the SAME labeled atoms.
This is a necessary local producer, not an assumed lower-diagram lift. -/
theorem comparison_eq {k : Kind} (D : AtomicData k A) :
    let z := LocalRanks.comparison k D.localRanks (D.frame (R:=R))
    z.left=z.right := by
  cases k with
  | passage m t => exact D.passage_comparison_eq
  | splitting a b c rev =>
    cases rev
    · exact D.split_comparison_eq
    · exact D.merge_comparison_eq

theorem comparison_holds {k : Kind} (D : AtomicData k A) :
    (LocalRanks.comparison k D.localRanks (D.frame (R:=R))).Holds := by
  let z := LocalRanks.comparison k D.localRanks (D.frame (R:=R))
  change SameFramedFlag z.grade z.left.linearEquiv z.right.linearEquiv
  have h : z.left=z.right := D.comparison_eq
  rw [h]
  exact MatrixIso.holds_self _ _

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.AtomicData
end

end OAI
