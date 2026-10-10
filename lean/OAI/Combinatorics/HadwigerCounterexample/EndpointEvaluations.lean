import OAI.Combinatorics.HadwigerCounterexample.PairIndexedTests
import OAI.Combinatorics.HadwigerCounterexample.BinaryPrescriptions

namespace OAI

/-! # Endpoint Evaluations -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

abbrev SameDuet (v : Template p I) :=
  {i : I×I//v.aim i.1=v.aim i.2 ∧ Fintype.equivFin I i.1<Fintype.equivFin I i.2}
abbrev OppDuet (v : Template p I) := {i:I×I//v.aim i.1=true∧v.aim i.2=false}
abbrev Chorus (v : Template p I) := v.SameDuet ⊕ v.OppDuet
instance : Fintype v.SameDuet := inferInstance
instance : Fintype v.OppDuet := inferInstance

def verses (v : Template p I) (x : v.Chorus) := x.elim Subtype.val Subtype.val
def choral (v : Template p I) : Stage I v.Chorus := {
  first := fun i => (v.verses i).1
  nextP := fun i => (v.verses i).2
  diff i := by
    rcases i with i|i
    · intro h; exact i.property.2.ne (congrArg (Fintype.equivFin I) h)
    intro h
    exact Bool.noConfusion (i.property.1.symm.trans ((congrArg v.aim h).trans i.property.2))
  once i j := by
    intro hi hj
    have he : v.verses i=v.verses j := Prod.ext hi hj
    rcases i with i|i <;> rcases j with j|j
    · exact congrArg _ (Subtype.ext (show i.val=j.val from he))
    · have hf : v.aim j.val.1=v.aim j.val.2 := (show i.val=j.val from he) ▸ i.property.1
      simp only [j.property] at hf; cases hf
    · have hf : v.aim i.val.1=v.aim i.val.2 := (show j.val=i.val from he.symm) ▸ j.property.1
      simp only [i.property] at hf; cases hf
    exact congrArg _ (Subtype.ext (show i.val=j.val from he))
  anti i j h h' := by
    rcases i with i|i <;> rcases j with j|j <;>
      change i.val.1=j.val.2 at h <;> change i.val.2=j.val.1 at h'
    · have hh := i.property.2; rw [h,h'] at hh; exact (not_lt_of_gt hh) j.property.2
    · have hh := i.property.1; rw [h,h',j.property.2,j.property.1] at hh; cases hh
    · have hh := j.property.1; rw [←h,←h',i.property.1,i.property.2] at hh; cases hh
    have hh := i.property.1; rw [h,j.property.2] at hh; cases hh }

abbrev Crossing (p : Shape) (i j : Tag p.g) :=
  {x : Notches p//inc x.1 i ∧ inc x.1 j}
abbrev Harm (p : Shape) := MBits p ⊕ Bool
def Abbey (v : Template p I) : v.Chorus → Type
  | .inl _ => Harm p
  | .inr x => Crossing p (v.t x.val.1) (v.t x.val.2)
instance (i : v.Chorus) : Fintype (v.Abbey i) :=
  i.rec (fun _ => inferInstanceAs (Fintype (Harm p))) (fun x => inferInstanceAs (Fintype
    (Crossing p (v.t x.val.1) (v.t x.val.2))))
instance (i : v.Chorus) : DecidableEq (v.Abbey i) := Classical.typeDecidableEq _

def monks (v : Template p I) (m : Mixer p n) (x : UnitType p n N) (i : v.Chorus) :
    v.Abbey i → Moment p n :=
  match i with
  | .inl _ => Sum.elim (fun l => eitherM l.2 (orderedM m l.1))
    (fun l => eitherM l (selfM p n m.mixM))
  | .inr _ => fun ⟨j,_⟩ => duel p (x.1 j.1) (x.2 j.1) j.2

def croon (v : Template p I) (i : I) := spring p (n:=n) (v.t i) (v.s i) (v.f i)

def chime (m : Mixer p n) (x : UnitType p n N)
    (i : v.Chorus) (y z : Knobs p.g n) : Vec (v.Abbey i) :=
  fun j => evmat (v.monks m x i j) (v.croon (v.choral.first i) y) (v.croon (v.choral.nextP i) z)

def chorusM (m : Mixer p n) (x : UnitType p n N)
    (i : v.Chorus) (y : Vec (v.Abbey i)) := ∑ j:v.Abbey i,y j • monks v m x i j

omit [DecidableEq I] in
theorem chime_seq (m : Mixer p n) (x : UnitType p n N) (i)
    (y : Vec (v.Abbey i)) (u z : Knobs p.g n) :
    dotProduct y (v.chime m x i u z)=evmat (v.chorusM m x i y)
      (v.croon (v.choral.first i) u) (v.croon (v.choral.nextP i) z) := by
  unfold chorusM dotProduct chime
  simp_rw [←mpair_outer, mpair_sum,mpair_smul]

omit [DecidableEq I] in
theorem chorus_same (m : Mixer p n) (x : UnitType p n N) (i : v.SameDuet)
    (y : Vec (v.Abbey (.inl i))) :
    v.chorusM m x (.inl i) y=indexedSum m (fun j => y (Sum.inl j)) + selfSum m (fun j => y (Sum.inr j)) := by
  unfold chorusM

  change ∑ j:Harm p,y j • monks v m x (.inl i) j=_
  rw [Fintype.sum_sum_type]; rfl

set_option maxHeartbeats 600000 in
omit [DecidableEq I] in
theorem chorus_cross (m : Mixer p n) (x : UnitType p n N) (i : v.OppDuet)
    (y : Vec (v.Abbey (.inr i))) (hy : y≠0) :
    ∃ w : Vec (Notches p), w≠0 ∧ v.chorusM m x (.inr i) y=issue p w x := by
  classical
  let T (j : Notches p) := inc j.1 (v.t i.val.1)∧inc j.1 (v.t i.val.2)
  let w (j : Notches p) := if h:T j then y (⟨j,h⟩ : Crossing p _ _) else 0
  have he (j : Crossing p (v.t i.val.1) (v.t i.val.2)) : w j.val=y j := dite_eq_left j.property
  have hz : w≠0 := fun h => hy (funext (fun j : Crossing p _ _ => by rw [←he,h]; rfl))
  refine ⟨w,hz,?_⟩
  let f (j : Notches p) := w j • duel p (x.1 j.1) (x.2 j.1) j.2
  have h : issue p w x=∑ i : Notches p,f i := by
    rw [Fintype.sum_prod_type]; rfl
  rw [h]
  have ht : ∑ j : {j:Notches p//T j},f j.val = ∑ j : Notches p,f j := by
    let s := univ.filter T
    rw [← Finset.sum_subtype s (by simp [s]) f]
    refine Finset.sum_subset (subset_univ _) (fun i _ hi => ?_)
    have hh : ¬T i := fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩)
    unfold f w; rw [dite_eq_right hh,zero_smul]
  rw [← ht]
  change (∑ j:{j:Notches p//T j},_) = _
  exact Finset.sum_congr rfl fun j _ => by unfold f; rw [he]; rfl
end Template
end HadwigerCounterexample

end

end OAI
