import OAI.Computability.MatchingCount.UnaryDivision

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def intParts (z : ℤ) : Bool×ℕ := (decide (z<0),z.natAbs)
def fromParts (p : Bool×ℕ) : ℤ := if p.1 then -(p.2:ℤ) else p.2
instance : Coding ℤ := ⟨fun z => encode (intParts z)⟩
@[simp] lemma encode_int (z : ℤ) : encode z=encode (intParts z) := rfl
lemma fromParts_parts (z : ℤ) : fromParts (intParts z)=z := by
  simp only [fromParts,intParts,decide_eq_true_eq]
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · exact Int.natAbs_of_nonneg (le_of_not_gt h)

lemma intParts_nat (n : ℕ) : intParts (n:ℤ)=(false,n) := by
  have h : ¬ (n:ℤ)<0 := by omega
  simp [intParts,h]
lemma intParts_fromParts (p : Bool×ℕ) :
    intParts (fromParts p)=(p.1 && !(decide (p.2=0)),p.2) := by
  rcases p with ⟨b,n⟩
  cases b with
  | false => simp [fromParts,intParts_nat]
  | true =>
    by_cases hn : n=0
    · subst n; simp [intParts,fromParts]
    · simp [intParts,fromParts,Nat.pos_iff_ne_zero,hn]

namespace Poly
@[fun_prop] theorem intParts_poly : Poly intParts := by
  exact ⟨(Routine.identity (encode : Bool×ℕ → List Bool)).reindex encode encode intParts intParts
    (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem natCastInt : Poly (Int.ofNat : ℕ → ℤ) := by
  have h : Poly (fun n : ℕ => (false,n)) := by fun_prop
  refine ⟨h.routine.reindex encode encode Int.ofNat id (fun _ => rfl) ?_⟩
  intro n
  change encode (false,n)=encode (intParts (n:ℤ))
  rw [intParts_nat]

@[fun_prop] theorem natToInt : Poly (fun n : ℕ => (n:ℤ)) := natCastInt

@[fun_prop] theorem fromParts_poly : Poly fromParts := by
  have h : Poly (fun p : Bool×ℕ => (p.1 && !(decide (p.2=0)),p.2)) := by
    apply pair
    · exact comp _ _ boolAnd (pair _ _ (by fun_prop) (comp _ _ boolNot (comp _ _ natZeroTest (by fun_prop))))
    · fun_prop
  refine ⟨h.routine.reindex encode encode fromParts id (fun _ => rfl) ?_⟩
  intro p
  simp only [id_eq,encode_int,intParts_fromParts]

@[fun_prop] theorem intNatAbs : Poly (Int.natAbs : ℤ → ℕ) := by
  have h : Poly (fun z : ℤ => (intParts z).2) := second _ intParts_poly
  exact h

@[fun_prop] theorem intSign : Poly (fun z : ℤ => decide (z<0)) := by
  have h : Poly (fun z : ℤ => (intParts z).1) := first _ intParts_poly
  exact h

@[fun_prop] theorem intNeg : Poly (fun z : ℤ => -z) := by
  have h : Poly (fun z : ℤ => fromParts (!(intParts z).1,(intParts z).2)) := by fun_prop
  exact h.congr (fun z => by cases z <;> simp [intParts,fromParts])

def addParts (p : (Bool×ℕ)×(Bool×ℕ)) : ℤ :=
  if p.1.1 then
    if p.2.1 then fromParts (true,p.1.2+p.2.2)
    else if decide (p.2.2≤p.1.2) then fromParts (true,p.1.2-p.2.2)
    else fromParts (false,p.2.2-p.1.2)
  else if p.2.1 then
    if decide (p.1.2≤p.2.2) then fromParts (true,p.2.2-p.1.2)
    else fromParts (false,p.1.2-p.2.2)
  else fromParts (false,p.1.2+p.2.2)

lemma addParts_eq (p q : Bool×ℕ) : addParts (p,q)=fromParts p+fromParts q := by
  rcases p with ⟨b,n⟩; rcases q with ⟨c,m⟩
  cases b <;> cases c <;> simp only [addParts,fromParts,Bool.false_eq_true,ite_false,ite_true,
    decide_eq_true_eq]
  · omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega

@[fun_prop] theorem intAdd : Poly (fun z : ℤ×ℤ => z.1+z.2) := by
  have ha : Poly addParts := by unfold addParts; fun_prop
  have h : Poly (fun z : ℤ×ℤ => addParts (intParts z.1,intParts z.2)) := by fun_prop
  exact h.congr (fun z => by rw [addParts_eq,fromParts_parts,fromParts_parts])

@[fun_prop] theorem intSub : Poly (fun z : ℤ×ℤ => z.1-z.2) := by
  have h : Poly (fun z : ℤ×ℤ => z.1+ -z.2) := by fun_prop
  exact h.congr (fun z => sub_eq_add_neg _ _)

@[fun_prop] theorem intMul : Poly (fun z : ℤ×ℤ => z.1*z.2) := by
  have hm : Poly (fun p : (Bool×ℕ)×(Bool×ℕ) => fromParts
      (if p.1.1 then !p.2.1 else p.2.1,p.1.2*p.2.2)) := by fun_prop
  have hp : Poly (fun z : ℤ×ℤ => (intParts z.1,intParts z.2)) :=
    pair _ _ (comp _ Prod.fst intParts_poly (first _ identity))
      (comp _ Prod.snd intParts_poly (second _ identity))
  have h := comp _ _ hm hp
  have he (p q : Bool×ℕ) :
      fromParts (if p.1 then !q.1 else q.1,p.2*q.2)=fromParts p*fromParts q := by
    rcases p with ⟨b,n⟩; rcases q with ⟨c,m⟩
    cases b <;> cases c <;> simp [fromParts]
  exact h.congr (fun z => by dsimp only; rw [he,fromParts_parts,fromParts_parts])

@[fun_prop] theorem intLE : Poly (fun z : ℤ×ℤ => decide (z.1≤z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => !(decide (z.2-z.1<0))) := by
    exact comp _ _ boolNot (comp _ _ intSign (comp _ (fun z : ℤ×ℤ => (z.2,z.1)) intSub (by fun_prop)))
  exact h.congr (fun z => by simp [←decide_not,sub_neg])

@[fun_prop] theorem intLT : Poly (fun z : ℤ×ℤ => decide (z.1<z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => decide (z.1-z.2<0)) := comp _ _ intSign intSub
  exact h.congr (fun z => by simp [sub_neg])

@[fun_prop] theorem intEQ : Poly (fun z : ℤ×ℤ => decide (z.1=z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => decide ((z.1-z.2).natAbs=0)) :=
    comp _ _ natZeroTest (comp _ _ intNatAbs intSub)
  exact h.congr (fun z => by simp [sub_eq_zero])

@[fun_prop] theorem intMin : Poly (fun z : ℤ×ℤ => min z.1 z.2) := by
  have h : Poly (fun z : ℤ×ℤ => if decide (z.1≤z.2) then z.1 else z.2) := by fun_prop
  exact h.congr (fun z => by simp [min_def])
@[fun_prop] theorem intMax : Poly (fun z : ℤ×ℤ => max z.1 z.2) := by
  have h : Poly (fun z : ℤ×ℤ => if decide (z.1≤z.2) then z.2 else z.1) := by fun_prop
  exact h.congr (fun z => by simp [max_def])
@[fun_prop] theorem intToNat : Poly (Int.toNat : ℤ → ℕ) := by
  have h : Poly (fun z : ℤ => if (intParts z).1 then 0 else (intParts z).2) := by fun_prop
  exact h.congr (fun z => by cases z <;> simp [intParts])
variable {α : Type} [Coding α]
@[fun_prop] theorem intLt_apply (f g : α → ℤ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a<g a)) := comp _ _ intLT (pair _ _ hf hg)
@[fun_prop] theorem intLe_apply (f g : α → ℤ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a≤g a)) := comp _ _ intLE (pair _ _ hf hg)
end Poly
end BinaryMatching.StackCode
end

end OAI
