import OAI.Combinatorics.HadwigerCounterexample.EndpointEvaluations

namespace OAI

/-! # Script Gram Correspondence -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

def lyrics (s : Script p I) (i : v.Chorus) : Vec (v.Abbey i) :=
  match i with
  | .inl z => Sum.elim (fun j => if j.2 then s z.val.1 z.val.2 j.1 else s z.val.2 z.val.1 j.1)
    (fun _ => 0)
  | .inr _ => 0
def performs (s : Script p I) (m : Mixer p n) (x : UnitType p n N) (z : Inputs p n I) :=
  listen v.choral (v.chime m x) z=v.lyrics s

omit [DecidableEq I] in
theorem across_duet (v : Template p I) {i j} (h : i ≠ j) :
    ∃ k : v.Chorus,v.verses k=(i,j)∨v.verses k=(j,i) := by
  classical
  let e := Fintype.equivFin I
  by_cases hg : v.aim i=v.aim j
  · rcases lt_or_gt_of_ne (e.injective.ne h) with hh|hh
    · exact ⟨.inl ⟨⟨i,j⟩,hg,hh⟩,Or.inl rfl⟩
    exact ⟨.inl ⟨⟨j,i⟩,hg.symm,hh⟩,Or.inr rfl⟩
  cases hi : v.aim i <;> cases hj : v.aim j
  · simp [hi,hj] at hg
  · exact ⟨.inr ⟨⟨j,i⟩,hj,hi⟩,Or.inr rfl⟩
  · exact ⟨.inr ⟨⟨i,j⟩,hi,hj⟩,Or.inl rfl⟩
  simp [hi,hj] at hg

def voices (v : Template p I) (x : Keys (p:=p) v.t N) (i j) (e : Comp p.g) (a : inc e (v.t i))
    (b : inc e (v.t j)) (q : Bool) :=
  dotProduct (x i ⟨e,a⟩ q) (x j ⟨e,b⟩ (!q))

omit [Fintype I] [DecidableEq I] in
theorem voice_note (v : Template p I) (x : UnitType p n N) (z : Inputs p n I)
    (e : Comp p.g) (i j) (a : inc e (v.t i)) (b : inc e (v.t j)) (q : Bool) :
    v.voices ((v.draw z).keys v.t x) i j e a b q=evmat
      (duel p (onSide x (v.aim i) e) (onSide x (v.aim j) e) q)
        (v.croon i (z i)) (v.croon j (z j)) := by
  let P := primary (takeSign (p:=p) (onSide x (v.aim i) e) q)
  let Q := primary (takeSign (p:=p) (onSide x (v.aim j) e) (!q))
  let u := v.croon i (z i); let t := v.croon j (z j)
  change dotProduct (P *ᵥ u) (Q *ᵥ t)=dotProduct u ((Pᵀ *Q)*ᵥ t)
  rw [← mulVec_mulVec,dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

omit [Fintype I] [DecidableEq I] in
theorem voice_same (v : Template p I) (x : UnitType p n N) (z : Inputs p n I)
    (m : Mixer p n) (hw : ∀ i,frameLaw m (onSide x i))
    (e : Comp p.g) (i j) (a : inc e (v.t i)) (b : inc e (v.t j))
    (h : v.aim i=v.aim j) (q : Bool) :
    v.voices ((v.draw z).keys v.t x) i j e a b q=evmat
      (eitherM q (selfM p n m.mixM)) (v.croon i (z i)) (v.croon j (z j)) := by
  rw [voice_note,h]
  let y := onSide x (v.aim j) e
  have he : (primary y.1)ᵀ*primary y.2=selfM p n m.mixM := (hw (v.aim j) e).2.2.1
  congr 1
  unfold duel
  cases q
  · change (primary y.2)ᵀ*primary y.1=_
    rw [←he]; simp only [eitherM,Bool.false_eq_true,ite_false, transpose_mul,transpose_transpose]
  exact he

def verges (v : Template p I) (x : Keys (p:=p) v.t N) (i j) :=
  ∀ e a b q,v.voices x i j e a b q=0
omit [Fintype I] [DecidableEq I] in
theorem verges_rev (v : Template p I) {x : Keys (p:=p) v.t N} {i j}
    (h : v.verges x i j) : v.verges x j i := by
  intro e a b q
  have ht := h e b a (!q)
  unfold voices at *; rw [dotProduct_comm]; rwa [Bool.not_not] at ht

omit [Fintype I] [DecidableEq I] in
theorem voices_diag (v : Template p I) (m : Mixer p n) (x : UnitType p n N)
    (w : Inputs p n I) (hw : ∀ i,frameLaw m (onSide x i)) (hj : 1≤p.j) (i : I) :
    ownOne p (v.t i) (dialed p (v.t i) (v.f i) (w i))
      ((v.draw w).keys v.t x i) := by
  intro e
  let y := (v.draw w).par i
  let A := mom p (v.s i) y
  have h : A∈Wspace p n := Submodule.subset_span ⟨_,_,rfl⟩
  have he := v.voice_same x w m hw e.val i i e.property e.property rfl true
  let E := selfM p n m.mixM
  change v.voices _ i i e.val e.property e.property true=_
  rw [he]
  change evmat E (point p _ y) (point p _ y)=_
  rw [← mpair_outer]
  exact (selfM_pair p hj m.mixM h).trans (etaScan p (n:=n) (v.t i) (v.s i) _ (w i)).symm

end Template
end HadwigerCounterexample

end

end OAI
