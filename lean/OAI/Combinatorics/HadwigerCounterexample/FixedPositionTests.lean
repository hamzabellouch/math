import OAI.Combinatorics.HadwigerCounterexample.UnaryCellComparisons
import OAI.Combinatorics.HadwigerCounterexample.KeyTestCorrespondence

namespace OAI

/-! # Fixed Position Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

def bolts (v : Template p I) {i j : I}
    (x : AtomKey (p:=p) (v.t i) N) (y : AtomKey (p:=p) (v.t j) N) :=
  ∀ e (h : inc e (v.t i)) (h' : inc e (v.t j)),
    dotProduct (x ⟨e,h⟩ true) (y ⟨e,h'⟩ false)=0 ∧
    dotProduct (y ⟨e,h'⟩ true) (x ⟨e,h⟩ false)=0
def boundTail (_ : Template p I) (j : I)
    (q : I→F) := fun i : Aside j => q i.val
def scriptTail (s : Script p I) (j : I) : Script p (Aside j) :=
  fun i k=> s i.val k.val

omit [Fintype I] in
theorem bolts_split (v : Template p I) (j : I) (q : I→F)
    (x : Keys (p:=p) v.t N) :
    ownPart (p:=p) v.t q x ↔
      ownOne p (v.t j) (q j) (x j) ∧ (∀ i:Aside j,v.bolts (x j) (x i.val)) ∧
      ownPart (p:=p) (v.beyond j).t (v.boundTail j q) ((v.chairK j N x).2) := by
  classical
  rw [ownPart_def,ownPart_def]
  let f (i k : I) := ∀ (e : Comp p.g) (h : inc e (v.t i)) (h' : inc e (v.t k)),
    i≠k→dotProduct (x i ⟨e,h⟩ true) (x k ⟨e,h'⟩ false)=0
  let r := v.beyond j
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨h1 j,fun k e a b=> ⟨h2 j k.val e a b (Ne.symm k.property),
      h2 k.val j e b a k.property⟩,fun i=> h1 i.val,?_⟩
    intro i k e a b hh; exact h2 _ _ e a b (fun ht=>hh (Subtype.ext ht))
  rintro ⟨h1,h2,h,h'⟩
  constructor
  · intro i
    by_cases hh:i=j
    · subst i; exact h1
    exact h ⟨i,hh⟩
  intro i k e a b hi
  by_cases he : i=j
  · subst i; exact (h2 ⟨k,Ne.symm hi⟩ e a b).1
  by_cases hh : k=j
  · subst k; exact (h2 ⟨i,hi⟩ e b a).2
  exact h' (⟨i,he⟩) (⟨k,hh⟩) e a b (fun h=>hi (congrArg Subtype.val h))

def huts (v : Template p I) (m : Mixer p n) (s : Script p I) (i k:I)
    (x y : Knobs p.g n) :=
  v.aim i=v.aim k → ∀ j:MOne p,
    s i k j=evmat (orderedM m j) (v.croon i x) (v.croon k y) ∧
    s k i j=evmat (orderedM m j) (v.croon k y) (v.croon i x)

omit [Fintype I] in
theorem read_split (v : Template p I) (j:I) (m : Mixer p n) (s : Script p I)
    (z : Inputs p n I) :
    (v.draw z).reads s m ↔
      (∀ i:Aside j,v.huts m s j i.val (z j) (z i.val)) ∧
      ((v.beyond j).draw (fun i => z i.val)).reads (scriptTail s j) m := by
  constructor
  · intro h
    constructor
    · exact fun i hA v=> ⟨h j i.val (Ne.symm i.property) hA v,h i.val j i.property
        (Eq.symm hA) v⟩
    intro x y he ha i; exact h x.val y.val (fun ht=>he (Subtype.ext ht)) ha i
  rintro ⟨h1,h2⟩ i k he ha d
  by_cases hh:i=j
  · subst i; exact (h1 ⟨k,Ne.symm he⟩ ha d).1
  by_cases hz:k=j
  · subst k; exact (h1 ⟨i,hh⟩ (Eq.symm ha) d).2
  exact h2 (⟨i,hh⟩) (⟨k,hz⟩) (fun h=>he (congrArg Subtype.val h)) ha d

def nib (v : Template p I) (o : UnitType p n N) (i : I) (z : Knobs p.g n) :=
  v.callOne i z (onSide o (v.aim i))

def lintel (v : Template p I) (j : I) (m : Mixer p n) (s : Script p I)
    (o : UnitType p n N) (x : Knobs p.g n) (i : Aside j) (z : Knobs p.g n) :=
  v.bolts (nib v o j x) (nib v o i.val z) ∧ v.huts m s j i.val x z

omit [Fintype I] in
theorem earns_split (v : Template p I) (j : I) (q : I→F) (m : Mixer p n) (s : Script p I)
    (o : UnitType p n N) (z : Inputs p n I) :
    earns v s m q o z↔ ownOne p (v.t j) (q j) (nib v o j (z j)) ∧
      (∀ i:Aside j,v.lintel j m s o (z j) i (z i.val)) ∧
      earns (v.beyond j) (scriptTail s j) m (v.boundTail j q) o
        (fun i:Aside j => z i.val) := by
  unfold earns lintel
  rw [read_split v j,bolts_split v j, key_split]
  have he (i : I) : resultKey v o z i=nib v o i (z i) := rfl
  simp_rw [he,forall_and]
  tauto
end Template
end HadwigerCounterexample

end

end OAI
