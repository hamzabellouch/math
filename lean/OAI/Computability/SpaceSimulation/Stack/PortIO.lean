import OAI.Computability.SpaceSimulation.Stack.Edit

namespace OAI

namespace Fifths.SM

/-! I/O adaptors. Scan the extra read-only tape into a stack; return
the heads home. Terminal values of fixed bit bound can be returned
directly in finite control. -/
variable {X K : Type} [DecidableEq K]

section Load

def inputSeek (d : Dir) (ops : K → StOp := fun _ => .keep) : StChange Unit K :=
  ⟨{darg := fun _ => d}, ops⟩

def endStep (r : Reads X Unit) (_ : K → Option Bool) :
    Option Unit × StChange Unit K :=
  match r.sarg () with
  | .right => (some (), .none)
  | _ => (none,inputSeek .R (fun _ => .keep))

def readStep (k : K) (r : Reads X Unit) (_ : K → Option Bool) :
    Option Unit × StChange Unit K :=
  match r.sarg () with
  | .left => (some (), .none)
  | .right => (none, inputSeek .L (fun _ => .keep))
  | .sym b => (none, inputSeek .L (Function.update (fun _ => .keep) k (.push b)))

def loader (k : K) : SM X Unit K Unit :=
  (act endStep).loop.seq (act (readStep k)).loop

def just (k : K) (l : List Bool) (p : ℕ) : Store Unit K :=
  ⟨{parg := fun _ => p}, fun y => if y = k then l else []⟩

theorem just_ok (k : K) (l : List Bool) (p) {B} (o : l.length ≤ B) :
    (just k l p).ok B := by
  intro y
  by_cases h : y = k <;> simp [just,h,o]

theorem loader_end (i : Inputs X Unit) (k : K) (B : ℕ) :
    (act endStep).loop.Exec i B (just k [] 0) (just k [] ((i.arg ()).length+1)) () := by
  let n := (i.arg ()).length
  have o (p : ℕ) : (just k [] p).ok B := just_ok _ _ _ (by simp)
  suffices h : ∀ l p, p+l = n+1 → (act endStep).loop.Exec i B (just k [] p)
      (just k [] (n+1)) () from h (n+1) 0 (by simp)
  intro l
  induction l with
  | zero =>
    intro p e
    have q : p = n+1 := by omega
    subst p
    refine loop_stop _ (exec_act (c := .none) ?_ (o _) (o _))
    have g : ((just k [] (n+1)).ro.see i).sarg () = .right :=
      (Mark.see_right ..).mpr (Nat.lt_succ_self n)
    simp [endStep,g]
  | succ l ih =>
    intro p e
    let s := just k [] p
    have g : (s.ro.see i).sarg () ≠ .right := by
      change Mark.see (i.arg ()) p ≠ _
      rw [ne_eq,Mark.see_right]
      have h : p ≤ n := by omega
      exact not_lt.mpr h
    let c : StChange Unit K := inputSeek .R (fun _ => .keep)
    have f : endStep (s.ro.see i) s.see = (none,c) := by
      cases h : (s.ro.see i).sarg ()
      · simp [endStep,h,c]
      · simp [endStep,h,c]
      · contradiction
    have j : s.perform i c = just k [] (p+1) := by
      refine Store.ext' ?_ ?_
      · dsimp [s,Store.perform,Readers.walk,c,just,inputSeek]
        congr
        funext y
        cases y
        have h : ¬ n < p := by omega
        simp [Mark.walk,show ¬(i.arg ()).length < p from h]
      · intro _; rfl
    have h := exec_act f (show s.ok B from o p) (j.symm ▸ o _)
    rw [j] at h
    exact loop_continue _ h (ih (p+1) (by omega))

theorem loader_start (i : Inputs X Unit) (k : K) {B : ℕ}
    (p : (i.arg ()).length ≤ B) :
    (act (readStep k)).loop.Exec i B
      (just k [] ((i.arg ()).length+1)) (just k (i.arg ()) 0) () := by
  let w := i.arg ()
  have g : ∀ l r : List Bool, w = l.reverse ++ r →
      (act (readStep k)).loop.Exec i B (just k r l.length) (just k w 0) () := by
    intro l
    induction l with
    | nil =>
      intro r e
      have eqn : r = w := by simpa using e.symm
      subst r
      have o : (just k w 0).ok B := just_ok _ _ _ p
      exact loop_stop _ (exec_act (c := .none) rfl o o)
    | cons a l ih =>
      intro r e
      have f : w = l.reverse ++ a :: r := by simpa using e
      have h : (a::r).length ≤ B := by
        change w.length ≤ B at p
        rw [f,List.length_append] at p
        omega
      let s := just k r (a::l).length
      have o : s.ok B := just_ok _ _ _ (by simp at h; omega)
      let c : StChange Unit K := inputSeek .L (Function.update (fun _ => .keep) k (.push a))
      have eqn : readStep k (s.ro.see i) s.see = (none,c) := by
        have m : (s.ro.see i).sarg () = .sym a := by
          change Mark.see w (_+1) = _
          simp [Mark.see,f]
        simp [readStep,m,c]
      have j : s.perform i c = just k (a::r) l.length := by
        refine Store.ext' ?_ ?_
        · dsimp [s,Store.perform,c,inputSeek,just,Readers.walk,Mark.walk]
        · intro y
          by_cases e : y = k <;> simp [Store.perform,c,inputSeek,s,just,e,StOp.apply]
      have v := exec_act eqn o (j.symm ▸ just_ok _ _ _ h)
      rw [j] at v
      exact loop_continue _ v (ih (a::r) f)
  let s := just k [] (w.length+1)
  have o : s.ok B := just_ok _ _ _ (by simp)
  let c : StChange Unit K := inputSeek .L (fun _ => .keep)
  have eqn : readStep k (s.ro.see i) s.see = (none,c) := by
    have m : (s.ro.see i).sarg () = .right :=
      (Mark.see_right ..).mpr (Nat.lt_succ_self w.length)
    simp [readStep,m,c]
  have j : s.perform i c = just k [] w.reverse.length := by
    refine Store.ext' ?_ ?_
    · dsimp [s,c,inputSeek,just,Store.perform,Readers.walk,Mark.walk]
      simp
    · intro _; rfl
  have v := exec_act eqn o (j.symm ▸ just_ok _ _ _ (show [].length ≤ B from Nat.zero_le _))
  rw [j] at v
  exact loop_continue _ v (g w.reverse [] (by simp))

theorem exec_loader (i : Inputs X Unit) (k : K) {B}
    (p : (i.arg ()).length ≤ B) :
    (loader k).Exec i B (Store.init (fun _ => [])) (just k (i.arg ()) 0) () := by
  have e : just k [] 0 = Store.init (fun _ => []) := by
    refine Store.ext' rfl ?_; simp [just,Store.init]
  rw [← e]
  exact exec_seq (loader_end i k _) (loader_start i k p)
end Load

section Decode
variable {J Y : Type}

/-- The (fixed) program is specialized to a maximum length. -/
def understand (k : K) : ℕ → (List Bool → Y) → SM X J K Y
  | 0,d => pure (d [])
  | n+1,d => (pop k).bind fun
    | none => pure (d [])
    | some b => understand k n (fun l => d (b :: l))

-- Zero length when trivial case, get empty; also restore to empty.
theorem exec_understand {i : Inputs X J} {s : Store J K} {B} (k : K) (n : ℕ)
    (d : List Bool → Y) (o : s.ok B) (h : (s.st k).length ≤ n) :
    (understand k n d).Exec i B s (s.set k []) (d (s.st k)) := by
  induction n generalizing s d with
  | zero =>
    have e : s.st k = [] := by simpa using h
    have f : s.set k [] = s := by rw [← e]; simp
    rw [e,f]
    exact exec_pure o
  | succ n ih =>
    have p := exec_pop (i := i) k o
    cases e : s.st k with
    | nil =>
      simp only [e,List.tail_nil,List.head?_nil] at p
      unfold understand
      refine exec_bind _ _ p ?_
      exact exec_pure p.endOk
    | cons b l =>
      simp only [e,List.tail_cons,List.head?_cons] at p
      unfold understand
      refine exec_bind _ _ p ?_
      have q := ih (fun l => d (b::l)) p.endOk (by simp; simpa [e] using h)
      simpa only [Store.set_set,Store.set_same] using q
end Decode
end Fifths.SM

end OAI
