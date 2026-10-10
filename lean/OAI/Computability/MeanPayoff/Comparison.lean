import OAI.Computability.MeanPayoff.BinaryData

namespace OAI

section

namespace MeanPayoff.ArithmeticForest
open RegisterBits
open BinaryData
open WorkStack

def placeA : Fin 3 → Fin 5 := ![0,2,4]
def placeB : Fin 3 → Fin 5 := ![0,3,4]
def placeAdd : Fin 3 → Fin 5 := ![2,3,4]
def placeBox : Fin 3 → Fin 5 := ![2,1,4]

theorem injectA : Function.Injective placeA := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [placeA]
theorem injectB : Function.Injective placeB := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [placeB]
theorem injectAdd : Function.Injective placeAdd := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [placeAdd]
theorem injectBox : Function.Injective placeBox := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [placeBox]

theorem installA (s : Fin 5 → List Bool) (a b c : List Bool) :
    install placeA s ![a,b,c] = ![a,s 1,b,s 3,c] := by
  funext i; fin_cases i
  · exact install_at placeA injectA s _ 0
  · exact install_off placeA s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeA injectA s _ 1
  · exact install_off placeA s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeA injectA s _ 2

theorem installB (s : Fin 5 → List Bool) (a b c : List Bool) :
    install placeB s ![a,b,c] = ![a,s 1,s 2,b,c] := by
  funext i; fin_cases i
  · exact install_at placeB injectB s _ 0
  · exact install_off placeB s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_off placeB s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeB injectB s _ 1
  · exact install_at placeB injectB s _ 2

theorem installAdd (s : Fin 5 → List Bool) (a b c : List Bool) :
    install placeAdd s ![a,b,c] = ![s 0,s 1,a,b,c] := by
  funext i; fin_cases i
  · exact install_off placeAdd s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_off placeAdd s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeAdd injectAdd s _ 0
  · exact install_at placeAdd injectAdd s _ 1
  · exact install_at placeAdd injectAdd s _ 2

theorem installBox (s : Fin 5 → List Bool) (a b c : List Bool) :
    install placeBox s ![a,b,c] = ![s 0,b,a,s 3,c] := by
  funext i; fin_cases i
  · exact install_off placeBox s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeBox injectBox s _ 1
  · exact install_at placeBox injectBox s _ 0
  · exact install_off placeBox s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeBox injectBox s _ 2

noncomputable abbrev flow : Flow.Program 5 where
  nodes := 4
  start := 0
  block q := match q with
    | 0 => rename Unbox.program placeA
    | 1 => rename Unbox.program placeB
    | 2 => rename (RegisterCompile.program WorkStack.SignedAddition.program) placeAdd
    | 3 => rename Box.program placeBox
  read _ := 4
  next q _ _ := match q with
    | 0 => some ⟨1,.keep,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | 2 => some ⟨3,.keep,none⟩
    | 3 => none

noncomputable def program := Flow.compile flow

def unboxTime (xs : List Bool) := feedCost xs+1+(2*xs.length+1)
def addTime (a b : SignedBits.Word) := 6*(2*max a.digits.length b.digits.length+5)
def boxTime (xs : List Bool) := 2*xs.length+2+feedCost xs+1

def addWord (a b : SignedBits.Word) := SignedBits.add a.sign b.sign false a.digits b.digits

def store0 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![encode (wordData a) ++ encode (wordData b) ++ xs, ys, [],[],[]]
def store1 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![encode (wordData b) ++ xs, ys, a.sign::a.digits,[],[]]
def store2 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs, ys, a.sign::a.digits,b.sign::b.digits,[]]
def store3 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs, ys, (addWord a b).sign::(addWord a b).digits,[],[]]
def store4 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs, encode (wordData (addWord a b))++ys, [],[],[]]

theorem stage0 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 0) bits ⟨some (flow.block 0).start, store0 a b xs ys, out⟩
      (unboxTime (a.sign::a.digits)) = ⟨none,store1 a b xs ys,out⟩ := by
  have h := rename_advance Unbox.program placeA injectA (store0 a b xs ys)
    (Unbox.cfg .read (encode (wordData a)++(encode (wordData b)++xs)) [] [] out)
    bits (unboxTime (a.sign::a.digits))
  rw [show unboxTime (a.sign::a.digits) = feedCost (a.sign::a.digits)+1+(2*(a.sign::a.digits).length+1) by rfl,
    show wordData a = listData (a.sign::a.digits) by rfl, Unbox.unboxes] at h
  simp only [renamed, Unbox.cfg, Unbox.stopped, installA, store0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three,
    List.append_nil, List.append_assoc] at h
  simp only [store0, List.append_assoc]
  convert h using 1 <;> rfl

theorem stage1 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 1) bits ⟨some (flow.block 1).start, store1 a b xs ys, out⟩
      (unboxTime (b.sign::b.digits)) = ⟨none,store2 a b xs ys,out⟩ := by
  have h := rename_advance Unbox.program placeB injectB (store1 a b xs ys)
    (Unbox.cfg .read (encode (wordData b)++xs) [] [] out)
    bits (unboxTime (b.sign::b.digits))
  rw [show unboxTime (b.sign::b.digits) = feedCost (b.sign::b.digits)+1+(2*(b.sign::b.digits).length+1) by rfl,
    show wordData b = listData (b.sign::b.digits) by rfl, Unbox.unboxes] at h
  simp only [renamed, Unbox.cfg, Unbox.stopped, installB, store1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, List.append_nil] at h
  convert h using 1 <;> rfl

theorem stage2 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 2) bits ⟨some (flow.block 2).start, store2 a b xs ys, out⟩
      (addTime a b) = ⟨none,store3 a b xs ys,out⟩ := by
  have h := rename_advance (RegisterCompile.program WorkStack.SignedAddition.program) placeAdd injectAdd
    (store2 a b xs ys) (RegisterCompile.lift WorkStack.SignedAddition.program out
      (WorkStack.SignedAddition.state .start (a.sign::a.digits) (b.sign::b.digits) []))
    bits (addTime a b)
  rw [show addTime a b = 6*(2*max a.digits.length b.digits.length+5) by rfl,
    RegisterCompile.signed_adds] at h
  simp only [renamed, RegisterCompile.lift, WorkStack.SignedAddition.state,
    WorkStack.SignedAddition.stopped, installAdd, store2, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  convert h using 1 <;> rfl

theorem stage3 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 3) bits ⟨some (flow.block 3).start, store3 a b xs ys, out⟩
      (boxTime ((addWord a b).sign::(addWord a b).digits)) = ⟨none,store4 a b xs ys,out⟩ := by
  have h := rename_advance Box.program placeBox injectBox (store3 a b xs ys)
    (Box.cfg .reverse ((addWord a b).sign::(addWord a b).digits) ys [] out)
    bits (boxTime ((addWord a b).sign::(addWord a b).digits))
  rw [show boxTime ((addWord a b).sign::(addWord a b).digits) =
    2*((addWord a b).sign::(addWord a b).digits).length+2+
      feedCost ((addWord a b).sign::(addWord a b).digits)+1 by rfl, Box.boxes] at h
  simp only [renamed, Box.cfg, Box.stopped, installBox, store3, Matrix.cons_val_zero, Matrix.cons_val_three] at h
  convert h using 1 <;> rfl

end MeanPayoff.ArithmeticForest

namespace MeanPayoff.ArithmeticForest
open RegisterBits
open BinaryData
open BinaryData.Take (advance_add)

theorem addWord_val (a b : SignedBits.Word) : (addWord a b).val = a.val+b.val := by
  cases a; cases b
  simpa [addWord] using
    SignedBits.add_val _ _ false _ _

theorem total_bound (a b : SignedBits.Word) :
    (unboxTime (a.sign::a.digits)+1) + (unboxTime (b.sign::b.digits)+1) +
      (addTime a b+1) + (boxTime ((addWord a b).sign::(addWord a b).digits)+1) ≤
      30*(a.digits.length+b.digits.length+3) := by
  have ha := Unbox.unboxes_bound (a.sign::a.digits)
  have hb := Unbox.unboxes_bound (b.sign::b.digits)
  have hc := Box.boxes_bound ((addWord a b).sign::(addWord a b).digits)
  have hl := SignedBits.add_length a.sign b.sign false a.digits b.digits
  change (addWord a b).digits.length = _ at hl
  simp only [List.length_cons] at ha hb hc
  unfold unboxTime addTime boxTime
  simp only [List.length_cons]
  omega

theorem program_adds (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    ∃ t ≤ 30*(a.digits.length+b.digits.length+3),
      advance program bits ⟨some program.start,store0 a b xs ys,out⟩ t =
        ⟨none,store4 a b xs ys,out⟩ := by
  obtain ⟨t₀,h₀,e₀⟩ := Flow.hop flow 0 1 (store0 a b xs ys) (store1 a b xs ys) out bits
    (unboxTime (a.sign::a.digits)) (stage0 a b xs ys out bits) (by intros; rfl)
  obtain ⟨t₁,h₁,e₁⟩ := Flow.hop flow 1 2 (store1 a b xs ys) (store2 a b xs ys) out
    (fun j => bits (t₀+j)) (unboxTime (b.sign::b.digits))
    (stage1 a b xs ys out _) (by intros; rfl)
  obtain ⟨t₂,h₂,e₂⟩ := Flow.hop flow 2 3 (store2 a b xs ys) (store3 a b xs ys) out
    (fun j => bits (t₀+t₁+j)) (addTime a b) (stage2 a b xs ys out _) (by intros; rfl)
  obtain ⟨t₃,h₃,e₃⟩ := Flow.finish flow 3 (store3 a b xs ys) (store4 a b xs ys) out
    (fun j => bits (t₀+t₁+t₂+j)) (boxTime ((addWord a b).sign::(addWord a b).digits))
    (stage3 a b xs ys out _) (by intros; rfl)
  refine ⟨t₀+t₁+t₂+t₃, le_trans (by omega) (total_bound a b), ?_⟩
  change advance (Flow.compile flow) bits (Flow.state flow 0 (store0 a b xs ys) out) _ = _
  rw [advance_add _ _ _ (t₀+t₁+t₂) t₃, advance_add _ _ _ (t₀+t₁) t₂,
    advance_add _ _ _ t₀ t₁, e₀, e₁, e₂, e₃]
  rfl

end MeanPayoff.ArithmeticForest

namespace MeanPayoff.SignedBits

def compareBit (x y c : Bool) : Bool := if x = y then c else !x && y

def compare (a b c : Bool) : List Bool → List Bool → Bool
  | [], [] => if a = b then c else a
  | x::xs, [] => compare a b (compareBit x b c) xs []
  | [], y::ys => compare a b (compareBit a y c) [] ys
  | x::xs, y::ys => compare a b (compareBit x y c) xs ys
termination_by xs ys => xs.length+ys.length

theorem compare_bit_correct (x y c : Bool) (A B : ℤ) :
    (A < B ∨ A = B ∧ compareBit x y c = true) ↔
      ((x.toNat : ℤ)+2*A < (y.toNat : ℤ)+2*B ∨
       (x.toNat : ℤ)+2*A = (y.toNat : ℤ)+2*B ∧ c = true) := by
  cases x <;> cases y <;> cases c <;> simp [compareBit] <;> omega

theorem compare_correct (a b c : Bool) (xs ys : List Bool) :
    compare a b c xs ys = true ↔
      (Word.mk a xs).val < (Word.mk b ys).val ∨
      (Word.mk a xs).val = (Word.mk b ys).val ∧ c = true := by
  cases xs with
  | nil =>
    cases ys with
    | nil => cases a <;> cases b <;> cases c <;> norm_num [compare, Word.val, BinaryStack.Addition.value]
    | cons y ys =>
      rw [compare, compare_correct, compare_bit_correct]
      have hx := val_uncons a []
      have hy := val_uncons b (y::ys)
      simp only [head, List.head?_nil, List.head?_cons, Option.getD_none, Option.getD_some,
        List.tail_nil, List.tail_cons] at hx hy
      rw [← hx, ← hy]
  | cons x xs =>
    cases ys with
    | nil =>
      rw [compare, compare_correct, compare_bit_correct]
      have hx := val_uncons a (x::xs)
      have hy := val_uncons b []
      simp only [head, List.head?_nil, List.head?_cons, Option.getD_none, Option.getD_some,
        List.tail_nil, List.tail_cons] at hx hy
      rw [← hx, ← hy]
    | cons y ys =>
      rw [compare, compare_correct, compare_bit_correct]
      have hx := val_uncons a (x::xs)
      have hy := val_uncons b (y::ys)
      simp only [head, List.head?_cons, Option.getD_some, List.tail_cons] at hx hy
      rw [← hx, ← hy]
termination_by xs.length+ys.length

theorem compare_lt (a b : Word) : compare a.sign b.sign false a.digits b.digits = true ↔ a.val < b.val := by
  cases a; cases b; simp [compare_correct]

end MeanPayoff.SignedBits

namespace MeanPayoff.WorkStack.SignedCompare
open SignedBits (compare compareBit)
inductive Label where
  | start
  | feed (a b c : Bool)
  | halt
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem decode (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply _

noncomputable def program : Program where
  states := Fintype.card Label
  start := enc .start
  transition q top _ := match equiv.symm q with
    | .start => some ⟨enc (.feed ((top 0).getD false) ((top 1).getD false) false), ![.pop,.pop,.keep]⟩
    | .feed a b c =>
      if top 0 = none ∧ top 1 = none then
        some ⟨enc .halt, ![.push (if a=b then c else a),.keep,.keep]⟩
      else some ⟨enc (.feed a b (compareBit ((top 0).getD a) ((top 1).getD b) c)), ![.pop,.pop,.keep]⟩
    | .halt => none
noncomputable def state (q : Label) (xs ys zs : List Bool) : Config program :=
  ⟨some (enc q), ![xs,ys,zs]⟩
def stopped (r : Bool) (zs : List Bool) : Config program := ⟨none, ![[r],[],zs]⟩

@[simp] theorem step_start (a b : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state .start (a::xs) (b::ys) zs) bit = state (.feed a b false) xs ys zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_nil (a b c : Bool) (zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) [] [] zs) bit = state .halt [if a=b then c else a] [] zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_left (a b c x : Bool) (xs zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) (x::xs) [] zs) bit = state (.feed a b (compareBit x b c)) xs [] zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_right (a b c y : Bool) (ys zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) [] (y::ys) zs) bit = state (.feed a b (compareBit a y c)) [] ys zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_both (a b c x y : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) (x::xs) (y::ys) zs) bit = state (.feed a b (compareBit x y c)) xs ys zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_halt (r : Bool) (zs : List Bool) (bit : Bool) :
    step program (state .halt [r] [] zs) bit = stopped r zs := by
  simp only [step,state,program,decode]; rfl

theorem feed_runs (a b c : Bool) (xs ys zs : List Bool) (bits : ℕ → Bool) :
    advance program bits (state (.feed a b c) xs ys zs) (max xs.length ys.length+1) =
      state .halt [compare a b c xs ys] [] zs := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp [advance,SignedBits.compare]
    | cons y ys =>
      rw [show max [].length (y::ys).length+1 = max [].length ys.length+1+1 by simp,
        advance_front, step_right, feed_runs]
      simp only [SignedBits.compare]
  | cons x xs =>
    cases ys with
    | nil =>
      rw [show max (x::xs).length [].length+1 = max xs.length [].length+1+1 by simp,
        advance_front, step_left, feed_runs]
      simp only [SignedBits.compare]
    | cons y ys =>
      rw [show max (x::xs).length (y::ys).length+1 = max xs.length ys.length+1+1 by simp,
        advance_front, step_both, feed_runs]
      simp only [SignedBits.compare]
termination_by xs.length+ys.length

theorem program_compares (a b : SignedBits.Word) (zs : List Bool) (bits : ℕ → Bool) :
    advance program bits (state .start (a.sign::a.digits) (b.sign::b.digits) zs)
      (max a.digits.length b.digits.length+3) =
      stopped (compare a.sign b.sign false a.digits b.digits) zs := by
  rw [show max a.digits.length b.digits.length+3 = (max a.digits.length b.digits.length+1+1)+1 by omega,
    advance_front, step_start, advance, feed_runs, step_halt]

theorem output_correct (a b : SignedBits.Word) (zs : List Bool) (bits : ℕ → Bool) :
    let c := advance program bits (state .start (a.sign::a.digits) (b.sign::b.digits) zs)
      (max a.digits.length b.digits.length+3)
    c.control = none ∧ (c.stack 0 = [true] ↔ a.val < b.val) ∧ c.stack 1 = [] ∧ c.stack 2 = zs := by
  simp only [program_compares,stopped,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    List.cons.injEq, and_true]
  exact ⟨True.intro, SignedBits.compare_lt a b, True.intro, rfl⟩
end MeanPayoff.WorkStack.SignedCompare
end

end OAI
