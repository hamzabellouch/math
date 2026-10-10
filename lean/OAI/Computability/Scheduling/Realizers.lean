import OAI.Computability.Scheduling.RoutineCompiler

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
namespace Data

def fold (f : Data → Data) (acc : Data) : Data → Data
  | .nil => acc
  | .pair a xs => fold f (f (.pair a acc)) xs

def foldCost (f : Data → Data) (c : Data → ℕ) (acc : Data) : Data → ℕ
  | .nil => 1
  | .pair a xs => c (.pair a acc) + foldCost f c (f (.pair a acc)) xs +
      20*((Data.pair a xs).size+acc.size+(f (.pair a acc)).size+1)

end Data
namespace Routine
variable {f : Data → Data} {c : Data → ℕ}

def foldStore (x acc xs : Data) : Fin 3 → Data := ![x,acc,xs]
@[simp] theorem foldStore_zero (x acc xs : Data) : foldStore x acc xs 0 = x := rfl
@[simp] theorem foldStore_one (x acc xs : Data) : foldStore x acc xs 1 = acc := rfl
@[simp] theorem foldStore_two (x acc xs : Data) : foldStore x acc xs 2 = xs := rfl

theorem foldStore_update_one (x acc xs y : Data) :
    Function.update (foldStore x acc xs) 1 y = foldStore x y xs := by
  funext i; fin_cases i <;> simp [foldStore]

theorem foldStore_update_two (x acc xs y : Data) :
    Function.update (foldStore x acc xs) 2 y = foldStore x acc y := by
  funext i; fin_cases i <;> simp [foldStore]

def foldBody (R : Routine f c) : Code (Fin 3 ⊕ R.Vars) :=
  .seq (.select true (.inr R.input) (.inl 2))
    (.seq (.pair (.inr R.input) (.inr R.input) (.inl 1))
    (.seq (R.code.rename Sum.inr)
    (.seq (.copy (.inl 1) (.inr R.output))
    (.seq (.nil (.inr R.input))
    (.seq (.nil (.inr R.output)) (.select false (.inl 2) (.inl 2)))))))

def foldCode (R : Routine f c) : Code (Fin 3 ⊕ R.Vars) :=
  .seq (.select true (.inl 2) (.inl 0))
    (.seq (.select false (.inl 1) (.inl 0)) (.loop (.inl 2) (foldBody R)))

theorem foldBody_correct (R : Routine f c) (x acc a xs : Data) :
    Bounded (foldBody R)
      (join (foldStore x acc (.pair a xs)) (zeroStore R.Vars))
      (join (foldStore x (f (.pair a acc)) xs) (zeroStore R.Vars))
      (c (.pair a acc)+20*((Data.pair a xs).size+acc.size+(f (.pair a acc)).size+1)-1) := by
  let l := foldStore x acc (.pair a xs)
  let l' := foldStore x (f (.pair a acc)) (.pair a xs)
  let z := zeroStore R.Vars
  let r := start R.input (.pair a acc)
  let r' := finish R.input R.output (.pair a acc) (f (.pair a acc))
  have h₁ : Bounded (.select true (.inr R.input) (.inl 2))
      (join l z) (join l (start R.input a)) (2+(Data.pair a xs).size) := by
    simpa [join_update_right,l,z,start,zeroStore,Data.head] using
      (Eval.select true (.inr R.input) (.inl 2) (join l z)).bounded
  have h₂ : Bounded (.pair (.inr R.input) (.inr R.input) (.inl 1))
      (join l (start R.input a)) (join l r) (1+a.size+a.size+acc.size) := by
    simpa [join_update_right,l,r,start,Function.update_idem] using
      (Eval.pair (.inr R.input) (.inr R.input) (.inl 1) (join l (start R.input a))).bounded
  have h₃ : Bounded (R.code.rename Sum.inr) (join l r) (join l r') (c (.pair a acc)) :=
    (R.correct (.pair a acc)).right l
  have h₄ : Bounded (.copy (.inl 1) (.inr R.output)) (join l r') (join l' r')
      (1+acc.size+(f (.pair a acc)).size) := by
    simpa [join_update_left,l,l',r',foldStore_update_one] using
      (Eval.copy (.inl 1) (.inr R.output) (join l r')).bounded
  have h₅ : Bounded (.nil (.inr R.input)) (join l' r')
      (join l' (start R.output (f (.pair a acc)))) (1+(Data.pair a acc).size) := by
    simpa only [join_update_right,r',reset_input R.distinct,join_inr,finish_input R.distinct] using
      (Eval.nil (.inr R.input) (join l' r')).bounded
  have h₆ : Bounded (.nil (.inr R.output))
      (join l' (start R.output (f (.pair a acc)))) (join l' z) (1+(f (.pair a acc)).size) := by
    simpa only [join_update_right,reset_start,join_inr,start_input,z] using
      (Eval.nil (.inr R.output) (join l' (start R.output (f (.pair a acc))))).bounded
  have h₇ : Bounded (.select false (.inl 2) (.inl 2)) (join l' z)
      (join (foldStore x (f (.pair a acc)) xs) z) (1+(Data.pair a xs).size+(Data.pair a xs).size) := by
    simpa [join_update_left,l',foldStore_update_two,Data.tail] using
      (Eval.select false (.inl 2) (.inl 2) (join l' z)).bounded
  have hh := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq h₇)))))
  exact hh.mono (by simp only [Data.size_pair]; omega)

theorem foldLoop_correct (R : Routine f c) (x acc xs : Data) :
    Bounded (.loop (.inl 2) (foldBody R))
      (join (foldStore x acc xs) (zeroStore R.Vars))
      (join (foldStore x (Data.fold f acc xs) .nil) (zeroStore R.Vars))
      (Data.foldCost f c acc xs) := by
  induction xs generalizing acc with
  | nil => exact Bounded.loop_stop _ _ _ rfl
  | pair a xs _ ih =>
    have hh := Bounded.loop_step (by rfl :
      ((join (foldStore x acc (.pair a xs)) (zeroStore R.Vars)) (.inl 2)).nonempty = true)
      (foldBody_correct R x acc a xs) (ih (f (.pair a acc)))
    exact hh.mono (by simp only [Data.foldCost]; omega)

def fold (R : Routine f c) :
    Routine (fun x => Data.fold f x.tail x.head)
      (fun x => 2*x.size+6+Data.foldCost f c x.tail x.head) where
  Vars := Fin 3 ⊕ R.Vars
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl 0
  output := .inl 1
  distinct := by simp
  code := foldCode R
  correct x := by
    have es : start (0 : Fin 3) x = foldStore x .nil .nil := by
      funext i; fin_cases i <;> simp [start,zeroStore,foldStore]
    have ef : finish (Sum.inl (0 : Fin 3)) (Sum.inl (1 : Fin 3)) x (Data.fold f x.tail x.head) =
        join (foldStore x (Data.fold f x.tail x.head) .nil) (zeroStore R.Vars) := by
      rw [finish,start_left,es,join_update_left,foldStore_update_one]
    have h₁ : Bounded (.select true (.inl 2) (.inl 0))
        (join (foldStore x .nil .nil) (zeroStore R.Vars))
        (join (foldStore x .nil x.head) (zeroStore R.Vars)) (2+x.size) := by
      simpa [join_update_left,foldStore_update_two] using
        (Eval.select true (.inl 2) (.inl 0)
          (join (foldStore x .nil .nil) (zeroStore R.Vars))).bounded
    have h₂ : Bounded (.select false (.inl 1) (.inl 0))
        (join (foldStore x .nil x.head) (zeroStore R.Vars))
        (join (foldStore x x.tail x.head) (zeroStore R.Vars)) (2+x.size) := by
      simpa [join_update_left,foldStore_update_one] using
        (Eval.select false (.inl 1) (.inl 0)
          (join (foldStore x .nil x.head) (zeroStore R.Vars))).bounded
    have hh := h₁.seq (h₂.seq (foldLoop_correct R x x.tail x.head))
    rw [start_left,es,ef]
    exact hh.mono (by omega)

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

class Coding (α : Type u1) where
  encode : α → Data

def enc {α : Type u2} [Coding α] : α → Data := Coding.encode

def volume {α : Type u3} [Coding α] (x : α) : ℕ := (enc x).size

instance : Coding Data := ⟨id⟩
instance : Coding Unit := ⟨fun _ => .nil⟩
instance : Coding Bool := ⟨fun b => if b then .pair .nil .nil else .nil⟩
instance {α : Type u4} {β : Type u5} [Coding α] [Coding β] : Coding (α × β) :=
  ⟨fun x => .pair (enc x.1) (enc x.2)⟩

def encodeList {α : Type u6} [Coding α] : List α → Data
  | [] => .nil
  | x :: xs => .pair (enc x) (encodeList xs)
instance {α : Type u7} [Coding α] : Coding (List α) := ⟨encodeList⟩

def encodeUnary : ℕ → Data | 0 => .nil | n+1 => .pair .nil (encodeUnary n)
instance : Coding ℕ := ⟨encodeUnary⟩
instance {α : Type u8} [Coding α] : Coding (Option α) :=
  ⟨fun x => match x with | none => .nil | some a => .pair (enc a) .nil⟩

@[simp] theorem enc_data (x : Data) : enc x = x := rfl
@[simp] theorem enc_unit (x : Unit) : enc x = .nil := rfl
@[simp] theorem enc_false : enc false = .nil := rfl
@[simp] theorem enc_true : enc true = .pair .nil .nil := rfl
@[simp] theorem enc_pair {α : Type u9} {β : Type u10} [Coding α] [Coding β] (x : α) (y : β) :
    enc (x,y) = .pair (enc x) (enc y) := rfl
@[simp] theorem enc_nil {α : Type u11} [Coding α] : enc ([] : List α) = .nil := rfl
@[simp] theorem enc_cons {α : Type u12} [Coding α] (x : α) (xs : List α) :
    enc (x :: xs) = .pair (enc x) (enc xs) := rfl
@[simp] theorem enc_zero : enc (0 : ℕ) = .nil := rfl
@[simp] theorem enc_succ (n : ℕ) : enc (n+1) = .pair .nil (enc n) := rfl
@[simp] theorem enc_none {α : Type u13} [Coding α] : enc (none : Option α) = .nil := rfl
@[simp] theorem enc_some {α : Type u14} [Coding α] (x : α) : enc (some x) = .pair (enc x) .nil := rfl

@[simp] theorem volume_pair {α : Type u15} {β : Type u16} [Coding α] [Coding β] (x : α) (y : β) :
    volume (x,y) = volume x+volume y+1 := Data.size_pair _ _
@[simp] theorem volume_nil {α : Type u17} [Coding α] : volume ([] : List α) = 1 := rfl
@[simp] theorem volume_cons {α : Type u18} [Coding α] (x : α) (xs : List α) :
    volume (x :: xs) = volume x+volume xs+1 := Data.size_pair _ _
@[simp] theorem volume_nat (n : ℕ) : volume n = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Data.size (.pair .nil (enc n)) = _
    change (enc n).size = 2*n+1 at ih
    simp only [Data.size_pair,Data.size_nil,ih]
    omega

structure Realizer {α : Type u19} {β : Type u20} [Coding α] [Coding β] (f : α → β) where
  transform : Data → Data
  charge : Data → ℕ
  routine : Routine transform charge
  correct : ∀ x, transform (enc x) = enc (f x)

namespace Realizer
variable {α : Type u21} {β : Type u22} {γ : Type u23} {δ : Type u24} [Coding α] [Coding β] [Coding γ] [Coding δ]
variable {f : α → β} {g : β → γ}

def time (R : Realizer f) (x : α) : ℕ := R.charge (enc x)

def id : Realizer (_root_.id : α → α) :=
  ⟨_root_.id,_,Routine.identity,fun _ => rfl⟩

@[simp] theorem time_id (x : α) : (id : Realizer (_root_.id : α → α)).time x = volume x+2 := rfl

def unit : Realizer (fun _ : α => ()) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ => rfl⟩

def nil : Realizer (fun _ : α => ([] : List β)) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ => rfl⟩

def zero : Realizer (fun _ : α => (0 : ℕ)) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ => rfl⟩

def false : Realizer (fun _ : α => Bool.false) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ => rfl⟩

def comp (R : Realizer f) (S : Realizer g) : Realizer (g ∘ f) where
  transform := S.transform ∘ R.transform
  charge := _
  routine := R.routine.comp S.routine
  correct x := by simp only [Function.comp_apply,R.correct,S.correct]

theorem time_comp (R : Realizer f) (S : Realizer g) (x : α) :
    (R.comp S).time x = R.time x+S.time (f x)+10*(volume (f x)+1) := by
  simp only [comp,time,Routine.comp,R.correct,volume]

def pair {g : α → γ} (R : Realizer f) (S : Realizer g) : Realizer (fun x => (f x,g x)) where
  transform := fun x => .pair (R.transform x) (S.transform x)
  charge := _
  routine := R.routine.pair S.routine
  correct x := by simp only [R.correct,S.correct,enc_pair]

theorem time_pair {g : α → γ} (R : Realizer f) (S : Realizer g) (x : α) :
    (R.pair S).time x = R.time x+S.time x+20*(volume x+volume (f x)+volume (g x)+1) := by
  simp only [pair,time,Routine.pair,R.correct,S.correct,volume]

def fst : Realizer (Prod.fst : α × β → α) :=
  ⟨Data.head,_,Routine.select true,fun _ => rfl⟩

def snd : Realizer (Prod.snd : α × β → β) :=
  ⟨Data.tail,_,Routine.select Bool.false,fun _ => rfl⟩

@[simp] theorem time_fst (x : α × β) : (fst : Realizer (Prod.fst : α × β → α)).time x = volume x+2 := rfl
@[simp] theorem time_snd (x : α × β) : (snd : Realizer (Prod.snd : α × β → β)).time x = volume x+2 := rfl

def congr {f' : α → β} (R : Realizer f) (h : ∀ x, f x = f' x) : Realizer f' :=
  { R with correct := fun x => (R.correct x).trans (congrArg enc (h x)) }

@[simp] theorem time_congr {f' : α → β} (R : Realizer f) (h : ∀ x, f x = f' x) (x : α) :
    (R.congr h).time x = R.time x := rfl

theorem fold_correct {F : α × β → β} (R : Realizer F) (xs : List α) (b : β) :
    Data.fold R.transform (enc b) (enc xs) = enc (xs.foldl (fun b a => F (a,b)) b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    change Data.fold R.transform (R.transform (enc (a,b))) (enc xs) = _
    rw [R.correct,ih]
    rfl

def fold {F : α × β → β} (R : Realizer F) :
    Realizer (fun x : List α × β => x.1.foldl (fun b a => F (a,b)) x.2) where
  transform := fun x => Data.fold R.transform x.tail x.head
  charge := _
  routine := R.routine.fold
  correct x := fold_correct R x.1 x.2

def foldTime {F : α × β → β} (R : Realizer F) (b : β) : List α → ℕ
  | [] => 1
  | a :: xs => R.time (a,b)+foldTime R (F (a,b)) xs+
      20*(volume (a :: xs)+volume b+volume (F (a,b))+1)

theorem foldTime_eq {F : α × β → β} (R : Realizer F) (xs : List α) (b : β) :
    Data.foldCost R.transform R.charge (enc b) (enc xs) = foldTime R b xs := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    change R.time (a,b)+Data.foldCost R.transform R.charge (R.transform (enc (a,b))) (enc xs)+
      20*(volume (a :: xs)+volume b+(R.transform (enc (a,b))).size+1) = _
    rw [R.correct,ih]
    rfl

theorem time_fold {F : α × β → β} (R : Realizer F) (x : List α × β) :
    R.fold.time x = 2*volume x+6+foldTime R x.2 x.1 := by
  change 2*volume x+6+Data.foldCost R.transform R.charge (enc x.2) (enc x.1) = _
  rw [foldTime_eq]

end Realizer
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {V : Type} [DecidableEq V]
theorem Bounded.branch_true {src : V} {p q : Code V} {s t : V → Data} {n : ℕ}
    (h : (s src).nonempty = true) (hp : Bounded p s t n) : Bounded (.branch src p q) s t (n+1) := by
  obtain ⟨m,hm,he⟩ := hp
  exact ⟨m+1,by omega,Eval.branch_true h he⟩
theorem Bounded.branch_false {src : V} {p q : Code V} {s t : V → Data} {n : ℕ}
    (h : (s src).nonempty = false) (hq : Bounded q s t n) : Bounded (.branch src p q) s t (n+1) := by
  obtain ⟨m,hm,he⟩ := hq
  exact ⟨m+1,by omega,Eval.branch_false h he⟩
end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}
variable {V : Type} [DecidableEq V]

def invoke (R : Routine f c) (dst src : V) : Code (V ⊕ R.Vars) :=
  .seq (.copy (.inr R.input) (.inl src))
    (.seq (R.code.rename Sum.inr)
    (.seq (.copy (.inl dst) (.inr R.output))
    (.seq (.nil (.inr R.input)) (.nil (.inr R.output)))))

theorem invoke_correct (R : Routine f c) (dst src : V) (s : V → Data) :
    Bounded (R.invoke dst src) (join s (zeroStore R.Vars))
      (join (Function.update s dst (f (s src))) (zeroStore R.Vars))
      (c (s src)+10*((s src).size+(s dst).size+(f (s src)).size+1)) := by
  let a := start R.input (s src)
  let b := finish R.input R.output (s src) (f (s src))
  let t := Function.update s dst (f (s src))
  have h₁ : Bounded (.copy (.inr R.input) (.inl src))
      (join s (zeroStore R.Vars)) (join s a) (2+(s src).size) := by
    simpa [join_update_right,a,start,zeroStore] using
      (Eval.copy (.inr R.input) (.inl src) (join s (zeroStore R.Vars))).bounded
  have h₂ := (R.correct (s src)).right s
  have h₃ : Bounded (.copy (.inl dst) (.inr R.output)) (join s b) (join t b)
      (1+(s dst).size+(f (s src)).size) := by
    simpa [join_update_left,t,b] using (Eval.copy (.inl dst) (.inr R.output) (join s b)).bounded
  have h₄ : Bounded (.nil (.inr R.input)) (join t b)
      (join t (start R.output (f (s src)))) (1+(s src).size) := by
    simpa only [join_update_right,b,reset_input R.distinct,join_inr,finish_input R.distinct] using
      (Eval.nil (.inr R.input) (join t b)).bounded
  have h₅ : Bounded (.nil (.inr R.output)) (join t (start R.output (f (s src))))
      (join t (zeroStore R.Vars)) (1+(f (s src)).size) := by
    simpa only [join_update_right,reset_start,join_inr,start_input] using
      (Eval.nil (.inr R.output) (join t (start R.output (f (s src))))).bounded
  exact (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))).mono (by omega)

def chooseCode (R : Routine f c) (S : Routine g d) : Code ((Fin 3 ⊕ R.Vars) ⊕ S.Vars) :=
  .seq (.select true (.inl (.inl 2)) (.inl (.inl 0)))
    (.seq (.branch (.inl (.inl 2))
      ((R.invoke (1 : Fin 3) 0).rename Sum.inl)
      (S.invoke (Sum.inl (1 : Fin 3)) (Sum.inl 0)))
      (.nil (.inl (.inl 2))))

def choose (R : Routine f c) (S : Routine g d) :
    Routine (fun x => if x.head.nonempty then f x else g x)
      (fun x => c x+d x+30*(x.size+(f x).size+(g x).size+1)) where
  Vars := (Fin 3 ⊕ R.Vars) ⊕ S.Vars
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl (.inl 0)
  output := .inl (.inl 1)
  distinct := by simp
  code := chooseCode R S
  correct x := by
    let z := zeroStore R.Vars
    let w := zeroStore S.Vars
    let s := foldStore x .nil .nil
    let s' := foldStore x .nil x.head
    let y := if x.head.nonempty then f x else g x
    let t := foldStore x y x.head
    have es : start (0 : Fin 3) x = s := by
      funext i; fin_cases i <;> simp [s,start,zeroStore,foldStore]
    have ef : finish (Sum.inl (Sum.inl (0 : Fin 3))) (Sum.inl (Sum.inl (1 : Fin 3))) x y =
        join (join (foldStore x y .nil) z) w := by
      rw [finish,start_left,start_left,es,join_update_left,join_update_left]
      simp only [s,foldStore_update_one]
      rfl
    have h₁ : Bounded (.select true (.inl (.inl 2)) (.inl (.inl 0)))
        (join (join s z) w) (join (join s' z) w) (2+x.size) := by
      simpa [join_update_left,s,s',foldStore_update_two] using
        (Eval.select true (.inl (.inl 2)) (.inl (.inl 0)) (join (join s z) w)).bounded
    have h₂ : Bounded (.branch (.inl (.inl 2)) ((R.invoke (1 : Fin 3) 0).rename Sum.inl)
        (S.invoke (Sum.inl (1 : Fin 3)) (Sum.inl 0)))
        (join (join s' z) w) (join (join t z) w)
        (c x+d x+10*(x.size+(f x).size+(g x).size+2)+1) := by
      cases he : x.head.nonempty with
      | false =>
        have hh := (S.invoke_correct (Sum.inl (1 : Fin 3)) (Sum.inl 0) (join s' z)).branch_false
          (src := Sum.inl (Sum.inl (2 : Fin 3))) (p := ((R.invoke (1 : Fin 3) 0).rename Sum.inl)) (by simpa [s'] using he)
        simpa only [join_update_left,s',foldStore_update_one,t,y,he,Bool.false_eq_true,ite_false,join_inl,foldStore_zero] using
          (hh.mono (m := c x+d x+10*(x.size+(f x).size+(g x).size+2)+1)
            (by simp only [join_inl,foldStore_zero,foldStore_one,s',Data.size_nil]; omega))
      | true =>
        have hh := ((R.invoke_correct (1 : Fin 3) 0 s').left w).branch_true
          (src := Sum.inl (Sum.inl (2 : Fin 3))) (q := S.invoke (Sum.inl (1 : Fin 3)) (Sum.inl 0)) (by simpa [s'] using he)
        simpa only [s',foldStore_update_one,t,y,he,ite_true,foldStore_zero] using
          (hh.mono (m := c x+d x+10*(x.size+(f x).size+(g x).size+2)+1)
            (by simp only [foldStore_zero,foldStore_one,s',Data.size_nil]; omega))
    have h₃ : Bounded (.nil (.inl (.inl 2))) (join (join t z) w)
        (join (join (foldStore x y .nil) z) w) (1+x.head.size) := by
      simpa only [join_update_left,t,foldStore_update_two,join_inl,foldStore_two] using
        (Eval.nil (.inl (.inl 2)) (join (join t z) w)).bounded
    rw [start_left,start_left,es,ef]
    have hh := h₁.seq (h₂.seq h₃)
    exact hh.mono (by
      have hx : x.head.size ≤ x.size := by cases x <;> simp [Data.head]; omega
      omega)

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Routine

def constant : (d : Data) → Routine (fun _ => d) (fun x => (2*d.size+1)*(20*x.size+50*d.size+50))
  | .nil => nil.mono (by intro x; simp only [Data.size_nil]; omega)
  | .pair a b => ((constant a).pair (constant b)).mono (by
      intro x
      simp only [Data.size_pair]
      nlinarith)

end Routine
namespace Realizer
variable {α : Type u25} {β : Type u26} {γ : Type u27} [Coding α] [Coding β] [Coding γ]

def constant (b : β) : Realizer (fun _ : α => b) :=
  ⟨fun _ => enc b,_,Routine.constant (enc b),fun _ => rfl⟩

def reinterpret (f : α → β) (h : ∀ x, enc (f x) = enc x) : Realizer f :=
  ⟨_root_.id,_,Routine.identity,fun x => (h x).symm⟩

@[simp] theorem time_reinterpret (f : α → β) (h : ∀ x, enc (f x) = enc x) (x : α) :
    (reinterpret f h).time x = volume x+2 := rfl

def cons : Realizer (fun x : α × List α => x.1 :: x.2) := reinterpret _ (fun _ => rfl)

def choose {f g : α → β} (R : Realizer f) (S : Realizer g) :
    Realizer (fun x : Bool × α => if x.1 then f x.2 else g x.2) where
  transform := fun x => if x.head.nonempty then (snd.comp R).transform x else (snd.comp S).transform x
  charge := _
  routine := (snd.comp R).routine.choose (snd.comp S).routine
  correct x := by
    rcases x with ⟨b,x⟩
    cases b <;> simp only [enc_pair,enc_false,enc_true,Data.head,Data.nonempty,
      Bool.false_eq_true,ite_false,ite_true]
    · exact (snd.comp S).correct (Bool.false,x)
    · exact (snd.comp R).correct (true,x)

theorem time_choose {f g : α → β} (R : Realizer f) (S : Realizer g) (x : Bool × α) :
    (R.choose S).time x = (snd.comp R).time x+(snd.comp S).time x+
      30*(volume x+volume (f x.2)+volume (g x.2)+1) := by
  change (snd.comp R).time x+(snd.comp S).time x+
    30*(volume x+((snd.comp R).transform (enc x)).size+((snd.comp S).transform (enc x)).size+1) = _
  rw [(snd.comp R).correct,(snd.comp S).correct]
  rfl

def ite {p : α → Bool} {f g : α → β} (P : Realizer p) (R : Realizer f) (S : Realizer g) :
    Realizer (fun x => if p x then f x else g x) :=
  ((P.pair id).comp (R.choose S)).congr (fun _ => rfl)

def succ : Realizer (fun n : ℕ => n+1) :=
  (unit.pair id).comp (reinterpret (fun x : Unit × ℕ => x.2+1) (by intro x; rfl)) |>.congr (fun _ => rfl)

end Realizer
end ThreeMachine.StackCompiler

end

end OAI
