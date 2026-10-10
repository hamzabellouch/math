import OAI.Computability.SpaceSimulation.Stack.Comp

namespace OAI

/-! Some elementary SM programs and their space bounds. We move by
popping into empty scratch stacks or onto stacks already in use; as
long as the end stacks of such a drain fit, the intermediate writes fit.
All lemmas here bound maximum height, not time. -/
namespace Fifths
variable {X J K : Type}

namespace Store
@[ext] theorem ext' {s t : Store J K} (r : s.ro = t.ro) (a : ∀ k, s.st k = t.st k) :
    s = t := by cases s; cases t; congr; exact funext a

def atX (s : Store J K) (p : ℕ) : Store J K :=
  ⟨{s.ro with px := p}, s.st⟩

def pre (s : Store J K) (dest : K → Bool) (l : List Bool) : Store J K :=
  ⟨s.ro, fun k => if dest k then l ++ s.st k else s.st k⟩

@[simp] theorem pre_nil (s : Store J K) (d : K → Bool) :
    s.pre d [] = s := by
  refine ext' rfl ?_; simp [pre]
@[simp] theorem pre_pre (s : Store J K) (d : K → Bool) (l m) :
    (s.pre d l).pre d m = s.pre d (m ++ l) := by
  refine ext' rfl ?_; intro k; cases e : d k <;> simp [pre,e]

section
variable [DecidableEq K]

def set (s : Store J K) (k : K) (l : List Bool) : Store J K :=
  ⟨s.ro, Function.update s.st k l⟩

@[simp] theorem set_ro (s : Store J K) (k l) : (s.set k l).ro = s.ro := rfl
@[simp] theorem set_same (s : Store J K) (k l) : (s.set k l).st k = l := by simp [set]
@[simp] theorem set_other (s : Store J K) {k y} (l) (h : y ≠ k) :
    (s.set k l).st y = s.st y := by simp [set,h]

@[simp] theorem set_set (s : Store J K) (k l m) : (s.set k l).set k m = s.set k m := by
  refine ext' rfl ?_; intro y; by_cases h : y = k <;> simp [h]
@[simp] theorem set_self (s : Store J K) (k) : s.set k (s.st k) = s := by simp [set]
theorem set_swap (s : Store J K) {k y} (h : y ≠ k) (l m) :
    (s.set k l).set y m = (s.set y m).set k l := by
  refine ext' rfl ?_
  intro z
  by_cases a : z = k
  · subst z; simp [Ne.symm h]
  by_cases b : z = y
  · subst z; simp [h]
  simp [a,b]

theorem set_ok {s : Store J K} {k l B} (o : s.ok B) (p : l.length ≤ B) :
    (s.set k l).ok B := by
  intro y
  by_cases h : y = k
  · simpa [h] using p
  · simpa [h] using o y

def drained (s : Store J K) (k : K) (d : K → Bool) (code : Bool → List Bool) :
    Store J K :=
  (s.set k []).pre d ((s.st k).reverse.flatMap code)

end
end Store

namespace SM
section Simple
variable [DecidableEq K]

def editOne (k : K) (a : StOp) : StChange J K :=
  ⟨{}, Function.update (fun _ => .keep) k a⟩

theorem perform_one (s : Store J K) (i : Inputs X J) (k : K) (a : StOp) :
    s.perform i (editOne k a) = s.set k (a.apply (s.st k)) := by
  refine Store.ext' rfl ?_; intro y
  by_cases h : y = k
  · subst y; simp [Store.perform,editOne]
  · simp [Store.perform,editOne,h,StOp.apply]

/-- Destructively peek (return none on empty). -/
def pop (k : K) : SM X J K (Option Bool) :=
  act (fun _ t => (t k, editOne k .pop))

theorem exec_pop {i : Inputs X J} {s : Store J K} {B} (k : K)
    (o : s.ok B) : (pop k).Exec i B s (s.set k (s.st k).tail) (s.st k).head? := by
  rw [show s.set k (s.st k).tail = s.perform i (editOne k .pop) from
    (perform_one s i k .pop).symm]
  refine exec_act rfl o ?_
  rw [perform_one]
  apply Store.set_ok o
  specialize o k
  cases e : s.st k with
  | nil => simp [StOp.apply]
  | cons a b => simp [e] at o; simp [StOp.apply]; omega

end Simple

/-- Push a fixed (top-first) string onto each selected stack. -/
def racks (d : K → Bool) (b : Bool) : StChange J K :=
  ⟨{}, fun k => if d k then .push b else .keep⟩

theorem racks_perform (s : Store J K) (i : Inputs X J) (d) (b) :
    s.perform i (racks d b) = s.pre d [b] := by
  refine Store.ext' rfl ?_; intro k; cases e : d k <;>
    simp [Store.perform, racks, StOp.apply, e, Store.pre]

def broadcast (d : K → Bool) : List Bool → SM X J K Unit
  | [] => pure ()
  | b :: l => (broadcast d l).seq (change (racks d b))

theorem exec_broadcast {i : Inputs X J} {s : Store J K} {B}
    (d : K → Bool) (l : List Bool)
    (o : s.ok B) (p : (s.pre d l).ok B) :
    (broadcast d l).Exec i B s (s.pre d l) () := by
  induction l with
  | nil => simpa [broadcast] using exec_pure (i := i) (y := ()) o
  | cons b l ih =>
    have h : (s.pre d l).ok B := by
      intro k; specialize p k
      cases e : d k
      · simpa [Store.pre,e] using p
      · simp [Store.pre,e] at *; omega
    have t : (s.pre d l).perform i (racks d b) = s.pre d (b :: l) := by
      simp [racks_perform]
    exact exec_seq (ih h)
      (t ▸ exec_change (racks d b) h (show ((s.pre d l).perform i (racks d b)).ok B from
        t.symm ▸ p))
section
variable [DecidableEq K]

def onto (k : K) : K → Bool := fun y => decide (y = k)

theorem pre_onto (s : Store J K) (k l) : s.pre (onto k) l = s.set k (l ++ s.st k) := by
  refine Store.ext' rfl ?_; intro y
  by_cases h : y = k <;> simp [Store.pre,h,onto]

def prepend (k : K) (l : List Bool) : SM X J K Unit := broadcast (onto k) l
theorem exec_prepend {i : Inputs X J} {s : Store J K} {B} (k : K) (l : List Bool)
    (o : s.ok B) (p : (l ++ s.st k).length ≤ B) :
    (prepend k l).Exec i B s (s.set k (l ++ s.st k)) () := by
  rw [← pre_onto]
  refine exec_broadcast _ _ o ?_
  rw [pre_onto]; exact Store.set_ok o p

/-- All symbols of one source stack flow to a number of destinations
(possibly zero), with each popped bit mapped to its own fixed code. -/
def drainBody (k : K) (d : K → Bool) (code : Bool → List Bool) :
    SM X J K (Option Unit) :=
  (pop k).bind fun
    | none => pure (some ())
    | some b => (broadcast d (code b)).seq (pure none)

def drain (k : K) (d : K → Bool) (code : Bool → List Bool) :
    SM X J K Unit :=
  (drainBody k d code).loop

theorem exec_drain {i : Inputs X J} {s : Store J K} {B}
    (k : K) (d : K → Bool) (code : Bool → List Bool) (dk : d k = false)
    (o : s.ok B) (p : (s.drained k d code).ok B) :
    (drain k d code).Exec i B s (s.drained k d code) () := by
  generalize h : s.st k = l
  induction l generalizing s with
  | nil =>
    have e₁ : (pop k).Exec i B s s none := by
      have e := exec_pop (i := i) k (s := s) o
      have g : s.set k [] = s := by rw [← h]; simp
      simpa [h,g] using e
    have e₂ : (drainBody k d code).Exec i B s s (some ()) := by
      unfold drainBody
      refine exec_bind _ _ e₁ ?_
      exact exec_pure o
    have r : s.drained k d code = s := by
      simp only [Store.drained,h,List.reverse_nil,List.flatMap_nil,Store.pre_nil]
      rw [← h]; simp
    rw [r]
    exact loop_stop _ e₂
  | cons b l ih =>
    let t := s.set k l
    have ot : t.ok B := by
      apply Store.set_ok o
      specialize o k
      simp [h] at o; omega
    let u := t.pre d (code b)
    have hu : u.st k = l := by simp [u,t,Store.pre,dk]
    have r : u.drained k d code = s.drained k d code := by
      simp only [Store.drained,h,hu]
      refine Store.ext' rfl ?_
      intro y
      by_cases hy : y = k
      · subst y; simp [Store.pre, dk]
      · cases e : d y <;> simp [Store.pre,hy,e,u,t]
    have ou : u.ok B := by
      rw [← r] at p
      intro y
      by_cases hy : y = k
      · subst y; simpa [hu,t] using ot k
      · specialize p y
        cases e : d y
        · simpa [Store.drained,Store.pre,e,hy] using p
        · simp [Store.drained,Store.pre,e,hy] at p; omega
    have e₁ : (pop k).Exec i B s t (some b) := by
      simpa [t,h] using exec_pop (i := i) k o
    have e₂ : (drainBody k d code).Exec i B s u none := by
      unfold drainBody
      refine exec_bind _ _ e₁ ?_
      exact exec_seq (exec_broadcast _ _ ot ou) (exec_pure ou)
    rw [← r]
    exact loop_continue _ e₂ (ih ou (r.symm ▸ p) hu)

def clear (k : K) : SM X J K Unit := drain k (fun _ => false) (fun _ => [])

theorem exec_clear {i : Inputs X J} {s : Store J K} {B} (k : K) (o : s.ok B) :
    (clear k).Exec i B s (s.set k []) () := by
  have h : s.drained k (fun _ => false) (fun _ => []) = s.set k [] := by
    refine Store.ext' rfl ?_; simp [Store.drained, Store.pre]
  rw [← h]
  exact exec_drain k _ _ rfl o (h.symm ▸ Store.set_ok o (by simp))

def spill (k y : K) : SM X J K Unit := drain k (onto y) (fun b => [b])
theorem exec_spill {i : Inputs X J} {s : Store J K} {B} (k y : K) (h : k ≠ y)
    (o : s.ok B) (p : (s.st k).length + (s.st y).length ≤ B) :
    (spill k y).Exec i B s ((s.set k []).set y ((s.st k).reverse ++ s.st y)) () := by
  have r : s.drained k (onto y) (fun b => [b]) =
      (s.set k []).set y ((s.st k).reverse ++ s.st y) := by
    simp [Store.drained,pre_onto,h.symm]
  rw [← r]
  refine exec_drain k _ _ (by simp [onto,h]) o ?_
  rw [r]
  apply Store.set_ok (Store.set_ok o (by simp))
  simpa using p
end

/-- Rewind only the public head. Does not need a position counter. -/
def rewind : SM X J K Unit :=
  (act (fun r _ =>
    match r.sx with
    | .left => (some (), .none)
    | _ => (none, (⟨{dx := .L}, fun _ => .keep⟩)))).loop

theorem exec_rewind {i : Inputs X J} {s : Store J K} {B} (o : s.ok B) :
    rewind.Exec i B s (s.atX 0) () := by
  let a (r : Reads X J) (_ : K → Option Bool) : Option Unit × StChange J K :=
    match r.sx with
    | .left => (some (), .none)
    | _ => (none, ⟨{dx := .L}, fun _ => .keep⟩)
  change (act a).loop.Exec _ _ _ _ _
  generalize h : s.ro.px = p
  induction p generalizing s with
  | zero =>
    have g : (s.ro.see i).sx = .left := by simp [Readers.see,h]
    have e : s.atX 0 = s := by rw [← h]; rfl
    rw [e]
    exact loop_stop _ (show (act a).Exec i B s s (some ()) from
      exec_act (c := .none) (by simp [a,g]) o o)
  | succ p ih =>
    have g : (s.ro.see i).sx ≠ .left := by simp [Readers.see,h]
    let c : StChange J K := ⟨{dx := .L}, fun _ => .keep⟩
    have e : a (s.ro.see i) s.see = (none,c) := by
      cases e : (s.ro.see i).sx with
      | left => contradiction
      | right => simp [a,e,c]
      | sym => simp [a,e,c]
    have r : s.perform i c = s.atX p := by
      simp [Store.perform,c,Readers.walk, Mark.walk,h,Store.atX,StOp.apply]
    have t : (s.atX p).ok B := o
    exact loop_continue _ (show (act a).Exec i B s (s.atX p) none from
      r ▸ exec_act e o (r.symm ▸ t))
      (ih t rfl)
end SM
end Fifths

end OAI
