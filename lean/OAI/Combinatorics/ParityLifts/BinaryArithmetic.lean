import OAI.Combinatorics.ParityLifts.BitPrograms

namespace OAI

namespace ParityWL.Complexity

def PolyProgram.natMul : PolyProgram (ℕ × ℕ) ℕ (fun x => x.1*x.2) := by
  let I := ((PolyProgram.fst ℕ ℕ).comp PolyProgram.ticks).pair
    ((PolyProgram.snd ℕ ℕ).comp PolyProgram.ticks)
  let P := (PolyProgram.snd Bool (List Bool)).mapWith
  refine ((I.comp P).comp (PolyProgram.flatten Bool) |>.comp (PolyProgram.length Bool)).congr ?_
  intro x
  simp [Function.comp_def]

def divStep (s : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × ℕ :=
  if s.1.1+1<s.2 then ((s.1.1+1,s.1.2),s.2) else ((0,s.1.2+1),s.2)

def PolyProgram.divStep : PolyProgram ((ℕ × ℕ) × ℕ) ((ℕ × ℕ) × ℕ) divStep := by
  let r := ((PolyProgram.fst (ℕ × ℕ) ℕ).comp (PolyProgram.fst ℕ ℕ)).comp PolyProgram.natSucc
  let q := (PolyProgram.fst (ℕ × ℕ) ℕ).comp (PolyProgram.snd ℕ ℕ)
  let t := PolyProgram.snd (ℕ × ℕ) ℕ
  let test := ((t.pair r).comp PolyProgram.natLe).comp (PolyProgram.not)
  exact (test.ite ((r.pair q).pair t) (((PolyProgram.const 0).pair (q.comp PolyProgram.natSucc)).pair t)).congr
    (by intro s; simp [Complexity.divStep,not_le])

lemma divStep_quotient (n t : ℕ) (ht : 0<t) :
    divStep ((n%t,n/t),t) = (((n+1)%t,(n+1)/t),t) := by
  have hr := Nat.mod_lt n ht
  have he := Nat.div_add_mod n t
  rw [Nat.mul_comm t] at he
  by_cases h : n%t+1<t
  · have he' : n+1 = (n/t)*t+(n%t+1) := by omega
    simp only [divStep,h,↓reduceIte]
    rw [he',Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt h]
    rw [Nat.add_comm ((n/t)*t),Nat.add_mul_div_right _ _ ht,Nat.div_eq_of_lt h,Nat.zero_add]
    rw [Nat.mod_eq_of_lt h]
  · have he' : n+1 = (n/t+1)*t := by nlinarith
    simp only [divStep,h,↓reduceIte]
    rw [he',Nat.mul_mod_left,Nat.mul_div_cancel _ ht]

lemma fold_divStep (xs : List Bool) (n t : ℕ) (ht : 0<t) :
    xs.foldl (fun s _ => divStep s) ((n%t,n/t),t) =
      (((n+xs.length)%t,(n+xs.length)/t),t) := by
  induction xs generalizing n with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons, divStep_quotient _ _ ht, ih]
    simp only [List.length_cons]
    rw [show n+1+xs.length=n+(xs.length+1) by omega]

def PolyProgram.natDivPos (t : ℕ) (ht : 0<t) : PolyProgram ℕ ℕ (fun n => n/t) := by
  let P := (PolyProgram.snd Bool ((ℕ × ℕ) × ℕ)).comp PolyProgram.divStep
  have hg (u : Bool) (s : (ℕ × ℕ) × ℕ) :
      (treeEncode (Complexity.divStep s)).size ≤ (treeEncode s).size+2*((treeEncode u).size+1)^0 := by
    simp only [Complexity.divStep]
    split <;> simp [DataTree.size]
    all_goals omega
  let F := P.foldlGrowing 2 0 hg
  let I := PolyProgram.ticks.pair (PolyProgram.const ((0,0),t))
  let R := (I.comp F).comp ((PolyProgram.fst (ℕ × ℕ) ℕ).comp (PolyProgram.snd ℕ ℕ))
  refine R.congr ?_
  intro n
  have he := fold_divStep (List.replicate n false) 0 t ht
  simpa [R,I,Function.comp_def] using congrArg (fun s => s.1.2) he

def PolyProgram.width (t : ℕ) (ht : 0<t) :
    PolyProgram ℕ ℕ (fun n => (n+t-1)/t) :=
  ((((PolyProgram.id ℕ).pair (PolyProgram.const (t-1))).comp PolyProgram.natAdd).comp
    (PolyProgram.natDivPos t ht)).congr (by intro n; change (n+(t-1))/t = _; rw [show n+(t-1)=n+t-1 by omega])

end ParityWL.Complexity

end OAI
