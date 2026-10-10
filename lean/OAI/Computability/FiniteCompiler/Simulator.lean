import OAI.Computability.FiniteCompiler.Validator

namespace OAI

/-!
Literal finite-quota machine simulation and readout correctness.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

/-- Finite work alphabet, including a literal code for every input letter and
    a distinct blank. The remaining symbols are rejected by output reading. -/
structure Alphabet (S Γ : Type*) where
  blank : Γ
  input : S → Γ
  output : Γ → Option S
  output_input : ∀ a, output (input a) = some a
  output_blank : output blank = none

inductive Move
  | stay | left | right
  deriving DecidableEq

instance : Fintype Move := ⟨{.stay, .left, .right}, by intro x; cases x <;> simp⟩

structure Command (Q Γ : Type*) where
  state : Q
  write : Γ
  move : Move
  deriving DecidableEq, Fintype

/-- A deterministic left-ended one-tape machine. `none` is halt, recognized
    only while the head is at a workspace cell. -/
structure Machine (Q Γ : Type*) where
  initial : Q
  transition : Q → Γ → Option (Command Q Γ)

inductive Resume (S : Type*)
  | input | fill : S → Resume S
  | spare | first | readout | put : S → Resume S
  deriving DecidableEq, Fintype

/-- Distinct phases make every scan's designated reading side unambiguous. -/
inductive Head (S Q : Type*)
  | start
  | rewind : Resume S → Head S Q
  | scan : Resume S → Head S Q
  | run : Q → Head S Q
  | left : Q → Head S Q
  | finish | ok
  deriving DecidableEq, Fintype

variable {S Γ Q : Type*}

/-- The cell table is finite when the alphabets and state set are finite. All
    tests and assignments are precisely the source's scan expansion. -/
def cell (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (q : Head S Q) (b : Base S) (t : Tag S Γ) :
    Option (Instruction (Head S Q) (Tag S Γ)) :=
  match q with
  | .start | .ok => none
  | .rewind s => some ⟨.rewind s,t,true⟩
  | .scan .input => match b with
    | .anchor a => if t.anchorRead then some ⟨q,t,true⟩
      else some ⟨.rewind (.fill a),{t with anchorRead := true},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan (.fill a) => match b with
    | .workspace => if t.workspaceFilled then some ⟨q,t,true⟩
      else some ⟨.rewind .input,{t with workspaceFilled := true, work := A.input a},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan .spare => match b with
    | .workspace => if t.workspaceFilled then some ⟨q,t,true⟩
      else some ⟨.rewind .first,t,false⟩
    | _ => some ⟨q,t,true⟩
  | .scan .first => match b with
    | .workspace => some ⟨.run M.initial,t,false⟩
    | _ => some ⟨q,t,true⟩
  | .run c => match b with
    | .workspace => match M.transition c t.work with
      | none => some ⟨.rewind .readout,t,false⟩
      | some d => some ⟨(if d.move = .left then .left d.state else .run d.state),
          {t with work := d.write}, d.move == .right⟩
    | _ => none
  | .left c => match b with
    | .workspace => some ⟨.run c,t,true⟩
    | .cutC => some ⟨.run c,t,false⟩
    | _ => none
  | .scan .readout => match b with
    | .workspace => if t.outputRead then some ⟨q,t,true⟩
      else if t.work = A.blank then some ⟨.finish,t,false⟩
      else (A.output t.work).map fun a => ⟨.rewind (.put a),{t with outputRead := true},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan (.put a) => match b with
    | .anchor _ => match t.output with
      | none => some ⟨.rewind .readout,{t with output := some a},false⟩
      | some _ => some ⟨q,t,true⟩
    | _ => some ⟨q,t,true⟩
  | .finish => some ⟨q,t,true⟩

def table (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] :
    Table (Head S Q) (Base S) (Tag S Γ) where
  direction
    | .rewind _ | .left _ => .left
    | _ => .right
  cell := cell A M
  boundary
    | .start => some (.rewind .input)
    | .rewind s => some (.scan s)
    | .scan .input => some (.rewind .spare)
    | .finish => some .ok
    | _ => none

/-- No false acceptance results from an attempted simulation past a quota edge. -/
theorem run_outside (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (q : Q) (b : Base S) (t : Tag S Γ) (hb : b ≠ .workspace) :
    (table A M).cell (.run q) b t = none := by
  cases b <;> simp_all [table, cell]

theorem ok_terminal (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) (hv : v.head = .ok) :
    Scan.step (table A M) v = none := by
  simp only [Scan.step, hv, table]
  split
  · simp [cell]
  · split <;> rfl

/-- Rewinding crosses all left cells unchanged and then changes phase at alpha.
    This lemma holds on dirty data as well as the intended clean simulation. -/
theorem rewind (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (s : Resume S) (l r : List (Base S × Tag S Γ)) (rb : Bool) :
    Relation.ReflTransGen (Scan.Step (table A M))
      ⟨l,.rewind s,r,true,rb⟩ ⟨[],.scan s,l.reverse ++ r,true,rb⟩ := by
  induction l generalizing r with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [Scan.Step, Scan.step, table]
  | cons a l ih =>
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        (Relation.ReflTransGen.head (by simp [Scan.Step, Scan.step, table, cell]) (ih (a::r)))

/-- Going to the right boundary also preserves every cell. -/
theorem finish (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (l r : List (Base S × Tag S Γ)) (lb : Bool) :
    Relation.ReflTransGen (Scan.Step (table A M))
      ⟨l,.finish,r,lb,true⟩ ⟨r.reverse ++ l,.ok,[],lb,true⟩ := by
  induction r generalizing l with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [Scan.Step, Scan.step, table]
  | cons a r ih =>
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        (Relation.ReflTransGen.head (by simp [Scan.Step, Scan.step, table, cell]) (ih (a::l)))

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*}

theorem cross_right (table : Table H B T) (q : H) (hd : table.direction q = .right)
    (p l r : List (B × T)) (lb rb : Bool)
    (hp : ∀ c ∈ p, table.cell q c.1 c.2 = some ⟨q,c.2,true⟩) :
    ReflTransGen (Step table) ⟨l,q,p ++ r,lb,rb⟩ ⟨p.reverse ++ l,q,r,lb,rb⟩ := by
  induction p generalizing l with
  | nil => exact .refl
  | cons c p ih =>
    rcases c with ⟨b,t⟩
    have hc := hp (b,t) (by simp)
    have hstep : Step table ⟨l,q,(b,t)::(p++r),lb,rb⟩
        ⟨(b,t)::l,q,p++r,lb,rb⟩ := by simp [Step, step, hd, hc]
    simpa only [List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append] using
      (ReflTransGen.head hstep (ih ((b,t)::l) fun c hc => hp c (by simp [hc])))

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

abbrev Cells (S Γ : Type*) := List (Base S × Tag S Γ)

/-- One complete find/update/rewind invocation acts on the first matching
    cell. No higher-level operation is used in the actual finite table. -/
theorem scan_update (s s' : Resume S) (p r : Cells S Γ) (b : Base S) (t t' : Tag S Γ)
    (hp : ∀ c ∈ p, cell A M (.scan s) c.1 c.2 = some ⟨.scan s,c.2,true⟩)
    (hc : cell A M (.scan s) b t = some ⟨.rewind s',t',false⟩) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan s,p ++ (b,t)::r,true,true⟩
      ⟨[],.scan s',p ++ (b,t')::r,true,true⟩ := by
  have h₀ := Scan.cross_right (table A M) (.scan s) rfl p [] ((b,t)::r) true true hp
  simp only [List.append_nil] at h₀
  have h₁ : Scan.Step (table A M)
      ⟨p.reverse,.scan s,(b,t)::r,true,true⟩
      ⟨p.reverse,.rewind s',(b,t')::r,true,true⟩ := by
    simp [Scan.Step, Scan.step, table, hc]
  have h₂ := rewind A M s' p.reverse ((b,t')::r) true
  simpa using (h₀.trans ((ReflTransGen.single h₁).trans h₂))

/-- Tags following the copy phase; unused full-tag fields remain literally
    clean, as required by the validator/simulator convention. -/
def readAnchor (a : S) (read : Bool) : Base S × Tag S Γ :=
  (.anchor a,{clean A.blank with anchorRead := read})

def filledWork (a : S) : Base S × Tag S Γ :=
  (.workspace,{clean A.blank with workspaceFilled := true, work := A.input a})

def bare (b : Base S) : Base S × Tag S Γ := (b,clean A.blank)

/-- The whole tape during copying: read and unread anchor prefixes on either
    side of the reserved workspace, with a filled prefix followed by blanks. -/
def body (xp xs yp ys w : List S) (n : ℕ) : Cells S Γ :=
  xp.map (readAnchor A · true) ++ xs.map (readAnchor A · false) ++
  [bare A .cutC] ++ w.map (filledWork A) ++ List.replicate n (bare A .workspace) ++
  [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)

def Pass (s : Resume S) (c : Base S × Tag S Γ) : Prop :=
  cell A M (.scan s) c.1 c.2 = some ⟨.scan s,c.2,true⟩

@[simp] theorem pass_read (a : S) : Pass A M .input (readAnchor A a true) := by
  rfl
@[simp] theorem pass_input_bareC : Pass A M .input (bare A .cutC) := by rfl
@[simp] theorem pass_input_bareD : Pass A M .input (bare A .cutD) := by rfl
@[simp] theorem pass_input_bareW : Pass A M .input (bare A .workspace) := by rfl
@[simp] theorem pass_input_filled (a : S) : Pass A M .input (filledWork A a) := by rfl
@[simp] theorem pass_fill_anchor (a b : S) (r : Bool) :
    Pass A M (.fill a) (readAnchor A b r) := by rfl
@[simp] theorem pass_fill_bareC (a : S) : Pass A M (.fill a) (bare A .cutC) := by rfl
@[simp] theorem pass_fill_filled (a b : S) : Pass A M (.fill a) (filledWork A b) := by rfl

/-- A loaded input letter is transferred to the next free workspace cell,
    expanding the prefix and shrinking the finite quota by one. -/
theorem copy_left_one (xp xs yp ys w : List S) (a : S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp (a::xs) yp ys w (n+1),true,true⟩
      ⟨[],.scan .input,body A (xp++[a]) xs yp ys (w++[a]) n,true,true⟩ := by
  let p := xp.map (readAnchor A · true)
  let r := xs.map (readAnchor A · false) ++ [bare A .cutC] ++
    w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
    [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
    (readAnchor A a false).2 (readAnchor A a true).2
    (by change ∀ c ∈ p, Pass A M .input c; simp [p]) (by rfl)
  let p' := (xp ++ [a]).map (readAnchor A · true) ++ xs.map (readAnchor A · false) ++
    [bare A .cutC] ++ w.map (filledWork A)
  let r' := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₂ := scan_update A M (.fill a) .input p' r' .workspace
    (clean A.blank) (filledWork A a).2
    (by
      change ∀ c ∈ p', Pass A M (.fill a) c
      intro c hc
      simp only [p', List.mem_append, List.mem_map, List.mem_singleton] at hc
      rcases hc with ((⟨b,_,rfl⟩ | ⟨b,_,rfl⟩) | rfl) | ⟨b,_,rfl⟩ <;> simp) (by rfl)
  have heq : (⟨[],Head.scan (.fill a),p ++ (.anchor a,(readAnchor A a true).2)::r,
      true,true⟩ : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) =
      ⟨[],.scan (.fill a),p' ++ (.workspace,clean A.blank)::r',true,true⟩ := by
    simp [p, r, p', r', List.replicate_succ, readAnchor, bare, List.append_assoc]
  rw [heq] at h₁
  simpa [body, p, r, p', r', List.replicate_succ, readAnchor, bare, filledWork,
    List.append_assoc] using h₁.trans h₂

theorem copy_right_one (xp yp ys w : List S) (a : S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp [] yp (a::ys) w (n+1),true,true⟩
      ⟨[],.scan .input,body A xp [] (yp++[a]) ys (w++[a]) n,true,true⟩ := by
  let p := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A) ++
    List.replicate (n+1) (bare A .workspace) ++ [bare A .cutD] ++
    yp.map (readAnchor A · true)
  let r := ys.map (readAnchor A · false)
  have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
    (readAnchor A a false).2 (readAnchor A a true).2
    (by
      change ∀ c ∈ p, Pass A M .input c
      intro c hc
      simp only [p, List.mem_append, List.mem_map, List.mem_singleton,
        List.mem_replicate] at hc
      rcases hc with ((((⟨b,_,rfl⟩ | rfl) | ⟨b,_,rfl⟩) | ⟨_,rfl⟩) | rfl) | ⟨b,_,rfl⟩ <;>
        simp) (by rfl)
  let p' := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A)
  let r' := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    (yp++[a]).map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₂ := scan_update A M (.fill a) .input p' r' .workspace
    (clean A.blank) (filledWork A a).2
    (by
      change ∀ c ∈ p', Pass A M (.fill a) c
      intro c hc
      simp only [p', List.mem_append, List.mem_map, List.mem_singleton] at hc
      rcases hc with (⟨b,_,rfl⟩ | rfl) | ⟨b,_,rfl⟩ <;> simp) (by rfl)
  have heq : (⟨[],Head.scan (.fill a),p ++ (.anchor a,(readAnchor A a true).2)::r,
      true,true⟩ : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) =
      ⟨[],.scan (.fill a),p' ++ (.workspace,clean A.blank)::r',true,true⟩ := by
    simp [p, r, p', r', List.replicate_succ, readAnchor, bare, List.append_assoc]
  rw [heq] at h₁
  simpa [body, p, r, p', r', List.replicate_succ, readAnchor, bare, filledWork,
    List.append_assoc] using h₁.trans h₂

theorem copy_left (xp xs yp ys w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp xs yp ys w (xs.length+n),true,true⟩
      ⟨[],.scan .input,body A (xp++xs) [] yp ys (w++xs) n,true,true⟩ := by
  induction xs generalizing xp w with
  | nil => simp; exact .refl
  | cons a xs ih =>
    have h := copy_left_one A M xp xs yp ys w a (xs.length+n)
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using h.trans (ih (xp++[a]) (w++[a]))

theorem copy_right (xp yp ys w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp [] yp ys w (ys.length+n),true,true⟩
      ⟨[],.scan .input,body A xp [] (yp++ys) [] (w++ys) n,true,true⟩ := by
  induction ys generalizing yp w with
  | nil => simp; exact .refl
  | cons a ys ih =>
    have h := copy_right_one A M xp yp ys w a (ys.length+n)
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using h.trans (ih (yp++[a]) (w++[a]))

/-- Both anchor blocks are copied in their order, not in zipper order. -/
theorem copy_all (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A [] x [] y [] (x.length+y.length+n),true,true⟩
      ⟨[],.scan .input,body A x [] y [] (x++y) n,true,true⟩ := by
  have h₁ := copy_left A M [] x [] y [] (y.length+n)
  have h₂ := copy_right A M x [] y x n
  simp only [List.nil_append] at h₁ h₂
  simpa only [Nat.add_assoc] using h₁.trans h₂

@[simp] theorem pass_spare_anchor (a : S) (r : Bool) :
    Pass A M .spare (readAnchor A a r) := by rfl
@[simp] theorem pass_spare_C : Pass A M .spare (bare A .cutC) := by rfl
@[simp] theorem pass_spare_filled (a : S) : Pass A M .spare (filledWork A a) := by rfl
@[simp] theorem pass_first_anchor (a : S) (r : Bool) :
    Pass A M .first (readAnchor A a r) := by rfl
@[simp] theorem pass_first_C : Pass A M .first (bare A .cutC) := by rfl

/-- The two final copy scans check a spare blank and position the machine at
    the first workspace cell. In particular the quota is not treated as tape
    that may silently grow during internal transitions. -/
theorem copy_enter_run (x y w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A x [] y [] w (n+1),true,true⟩
      ⟨(x.map (readAnchor A · true) ++ [bare A .cutC]).reverse,.run M.initial,
        w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),true,true⟩ := by
  let cells := body A x [] y [] w (n+1)
  have hall : ∀ c ∈ cells, Pass A M .input c := by
    simp only [cells, body, List.map_nil, List.append_nil, List.forall_mem_append,
      List.forall_mem_map, List.forall_mem_singleton, List.forall_mem_replicate]
    simp
  have h₀ := Scan.cross_right (table A M) (.scan .input) rfl cells [] [] true true hall
  have h₁ : Scan.Step (table A M) ⟨cells.reverse,.scan .input,[],true,true⟩
      ⟨cells.reverse,.rewind .spare,[],true,true⟩ := by
    simp [Scan.Step, Scan.step, table]
  have h₂ := rewind A M .spare cells.reverse [] true
  simp only [List.reverse_reverse, List.append_nil] at h₀ h₂
  have hpre := h₀.trans ((ReflTransGen.single h₁).trans h₂)
  let p := x.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A)
  let r := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    y.map (readAnchor A · true)
  have hs := scan_update A M .spare .first p r .workspace (clean A.blank) (clean A.blank)
    (by
      change ∀ c ∈ p, Pass A M .spare c
      simp only [p, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
      simp) (by rfl)
  have heq : cells = p ++ (.workspace,clean A.blank)::r := by
    simp [cells, body, p, r, bare, List.replicate_succ, List.append_assoc]
  rw [← heq] at hs
  let p' := x.map (readAnchor A · true) ++ [bare A .cutC]
  let r' := w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
    [bare A .cutD] ++ y.map (readAnchor A · true)
  have hp' : ∀ c ∈ p', Pass A M .first c := by
    simp only [p', List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
    simp
  have hf := Scan.cross_right (table A M) (.scan .first) rfl p' [] r' true true hp'
  have hnonempty : ∃ t tail, r' = (.workspace,t)::tail := by
    cases w with
    | nil => exact ⟨clean A.blank,r,by simp [r', r, bare, List.replicate_succ, List.append_assoc]⟩
    | cons a w =>
      exact ⟨(filledWork A a).2,
        w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),
        by simp [r', filledWork, List.append_assoc]⟩
  have hlast : Scan.Step (table A M) ⟨p'.reverse,.scan .first,r',true,true⟩
      ⟨p'.reverse,.run M.initial,r',true,true⟩ := by
    obtain ⟨tag,tail,hr⟩ := hnonempty
    simp [Scan.Step, Scan.step, table, cell, hr]
  have heq' : cells = p' ++ r' := by simp [cells, body, p', r', List.append_assoc]
  rw [← heq'] at hf
  simp only [List.append_nil] at hf
  exact hpre.trans (hs.trans (hf.tail hlast))

/-- The fresh post-validator handoff starts copying from the left boundary. -/
theorem start_copy (cells : Cells S Γ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨cells.reverse,.start,[],true,true⟩ ⟨[],.scan .input,cells,true,true⟩ := by
  have h₀ : Scan.Step (table A M) ⟨cells.reverse,.start,[],true,true⟩
      ⟨cells.reverse,.rewind .input,[],true,true⟩ := by
    simp [Scan.Step, Scan.step, table]
  simpa using (ReflTransGen.head h₀ (rewind A M .input cells.reverse [] true))

/-- Literal correctness of the complete copy/init program with any sufficient
    finite quota. Every table operation is one of the listed compiled equations. -/
theorem copy_correct (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩
      ⟨(x.map (readAnchor A · true) ++ [bare A .cutC]).reverse,.run M.initial,
        (x++y).map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),true,true⟩ := by
  have h₀ := start_copy A M (body A [] x [] y [] (x.length+y.length+(n+1)))
  have h₁ := copy_all A M x y (n+1)
  have h₂ := copy_enter_run A M x y (x++y) n
  simpa only [Nat.add_assoc] using h₀.trans (h₁.trans h₂)

end

section
open Relation
variable {S Γ Q : Type*}

/-- A literal bounded workspace. The left list is in reverse tape order, and
    an empty right list is outside the supplied quota, not a fresh blank cell. -/
structure Tape where
  state : Q
  left : List (Tag S Γ)
  right : List (Tag S Γ)

/-- Update only the simulated work track; all auxiliary tag fields are retained. -/
def writeWork (t : Tag S Γ) (a : Γ) : Tag S Γ := { t with work := a }

/-- The intended finite-quota operations of the finite compiler. These are
    defined from the given machine table, not postulated accepting transitions. -/
inductive TapeStep (M : Machine Q Γ) : Tape (S := S) (Γ := Γ) (Q := Q) → Tape → Prop
  | stay {q l t r d} (h : M.transition q t.work = some d) (hm : d.move = .stay) :
      TapeStep M ⟨q,l,t::r⟩ ⟨d.state,l,writeWork t d.write::r⟩
  | right {q l t r d} (h : M.transition q t.work = some d) (hm : d.move = .right) :
      TapeStep M ⟨q,l,t::r⟩ ⟨d.state,writeWork t d.write::l,r⟩
  | leftEdge {q t r d} (h : M.transition q t.work = some d) (hm : d.move = .left) :
      TapeStep M ⟨q,[],t::r⟩ ⟨d.state,[],writeWork t d.write::r⟩
  | left {q v l t r d} (h : M.transition q t.work = some d) (hm : d.move = .left) :
      TapeStep M ⟨q,v::l,t::r⟩ ⟨d.state,l,v::writeWork t d.write::r⟩

def workCells (l : List (Tag S Γ)) : Cells S Γ := l.map fun t => (.workspace,t)

/-- Workspace in its fixed surrounding anchor/cut sector. `x` is the cells
    before C in their ordinary order, `y` the cells following D. -/
def runSector (A : Alphabet S Γ) (x y : Cells S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    Scan.Sector (Head S Q) (Base S) (Tag S Γ) :=
  ⟨workCells c.left ++ bare A .cutC :: x.reverse, .run c.state,
    workCells c.right ++ bare A .cutD :: y, true, true⟩

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- Every bounded machine transition is implemented by one or two actual
    finite scan instructions. Both the stationary left edge and true left
    movement are proved, and no quota insertion occurs during simulation. -/
theorem tapeStep_simulates (x y : Cells S Γ) {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : TapeStep M c d) :
    ReflTransGen (Scan.Step (table A M)) (runSector A x y c) (runSector A x y d) := by
  cases h with
  | stay h hm =>
      apply ReflTransGen.single
      simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
  | right h hm =>
      apply ReflTransGen.single
      simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
  | @leftEdge q t r d h hm =>
      apply ReflTransGen.trans (b :=
        ⟨bare A .cutC :: x.reverse, .left d.state,
          (.workspace, writeWork t d.write) :: (workCells r ++ bare A .cutD :: y), true,true⟩)
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, bare]
  | @left q v l t r d h hm =>
      apply ReflTransGen.trans (b :=
        ⟨(.workspace,v) :: (workCells l ++ bare A .cutC :: x.reverse), .left d.state,
          (.workspace, writeWork t d.write) :: (workCells r ++ bare A .cutD :: y),true,true⟩)
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells]

/-- Simulation respects literal finite traces, without a running-time bound. -/
theorem tapeRun_simulates (x y : Cells S Γ) {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : ReflTransGen (TapeStep M) c d) :
    ReflTransGen (Scan.Step (table A M)) (runSector A x y c) (runSector A x y d) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (tapeStep_simulates A M x y hs)

/-- Exhaustion is stuck even if the machine's current state would be halting:
    a halt must be observed at an actual workspace cell. -/
theorem quota_exhausted (x y : Cells S Γ) (q : Q) (l : List (Tag S Γ)) :
    Scan.step (table A M) (runSector A x y ⟨q,l,[]⟩) = none := by
  simp [Scan.step, table, cell, runSector, workCells, bare]

/-- A genuine in-bounds halt triggers precisely the readout rewind. -/
theorem halt_readout (x y : Cells S Γ) (q : Q) (l : List (Tag S Γ))
    (t : Tag S Γ) (r : List (Tag S Γ)) (h : M.transition q t.work = none) :
    ReflTransGen (Scan.Step (table A M))
      (runSector A x y ⟨q,l,t::r⟩)
      ⟨[],.scan .readout,
        x ++ [bare A .cutC] ++ workCells (l.reverse ++ t::r) ++ bare A .cutD :: y,
        true,true⟩ := by
  have hs : Scan.Step (table A M) (runSector A x y ⟨q,l,t::r⟩)
      ⟨workCells l ++ bare A .cutC :: x.reverse, .rewind .readout,
        workCells (t::r) ++ bare A .cutD :: y, true,true⟩ := by
    simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h]
  have hr := rewind A M .readout (workCells l ++ bare A .cutC :: x.reverse)
    (workCells (t::r) ++ bare A .cutD :: y) true
  simpa [workCells, List.reverse_append, List.reverse_cons, List.map_reverse,
    List.append_assoc] using ((ReflTransGen.single hs).trans hr)

end

section
open Relation
variable {S Γ Q : Type*}

/-- Locate a specified item of a projected list without discarding the cells
    skipped by the projection. This handles interleaved anchors and workspace. -/
theorem split_filterMap {α β : Type*} (f : α → Option β) (l : List α)
    (p : List β) (b : β) (r : List β) (h : l.filterMap f = p ++ b::r) :
    ∃ l₁ a l₂, l = l₁ ++ a::l₂ ∧ l₁.filterMap f = p ∧
      f a = some b ∧ l₂.filterMap f = r := by
  induction l generalizing p with
  | nil => simp at h
  | cons a l ih =>
      cases hf : f a with
      | none =>
          simp only [List.filterMap_cons, hf] at h
          obtain ⟨l₁,c,l₂,hl,hp,hc,hr⟩ := ih p h
          exact ⟨a::l₁,c,l₂,by simp [hl],by simp [hf,hp],hc,hr⟩
      | some v =>
          simp only [List.filterMap_cons, hf] at h
          cases p with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at h
              exact ⟨[],a,l,by simp, rfl,by simpa [h.1] using hf,h.2⟩
          | cons v' p =>
              simp only [List.cons_append, List.cons.injEq] at h
              obtain ⟨l₁,c,l₂,hl,hp,hc,hr⟩ := ih p h.2
              exact ⟨a::l₁,c,l₂,by simp [hl],by simp [hf,hp,h.1],hc,hr⟩

def workView (l : Cells S Γ) : List (Bool × Γ) :=
  l.filterMap fun c => match c.1 with
    | .workspace => some (c.2.outputRead,c.2.work)
    | _ => none

def anchorView (l : Cells S Γ) : List (Option S) :=
  l.filterMap fun c => match c.1 with
    | .anchor _ => some c.2.output
    | _ => none

@[simp] theorem workView_append (l r : Cells S Γ) :
    workView (l ++ r) = workView l ++ workView r := List.filterMap_append
@[simp] theorem anchorView_append (l r : Cells S Γ) :
    anchorView (l ++ r) = anchorView l ++ anchorView r := List.filterMap_append

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem readout_pass (l : Cells S Γ) (done : List Γ)
    (h : workView l = done.map (true,·)) :
    ∀ c ∈ l, cell A M (.scan .readout) c.1 c.2 = some ⟨.scan .readout,c.2,true⟩ := by
  rintro ⟨b,t⟩ hc
  cases b <;> try rfl
  have ht : (t.outputRead,t.work) ∈ workView l :=
    List.mem_filterMap.mpr ⟨(.workspace,t),hc,rfl⟩
  rw [h] at ht
  obtain ⟨v,_,hv⟩ := List.mem_map.mp ht
  have hr : t.outputRead = true := (congrArg Prod.fst hv).symm
  simp [cell, hr]

theorem put_pass (a : S) (l : Cells S Γ) (done : List S)
    (h : anchorView l = done.map some) :
    ∀ c ∈ l, cell A M (.scan (.put a)) c.1 c.2 = some ⟨.scan (.put a),c.2,true⟩ := by
  rintro ⟨b,t⟩ hc
  cases b <;> try rfl
  rename_i b
  have ht : t.output ∈ anchorView l := List.mem_filterMap.mpr ⟨(.anchor b,t),hc,rfl⟩
  rw [h] at ht
  obtain ⟨v,_,hv⟩ := List.mem_map.mp ht
  simp [cell, ← hv]

/-- One output letter is read from the first unread workspace cell and written
    to the first unmarked anchor. The projected views certify both orders. -/
theorem readout_one (cells : Cells S Γ) (done remaining : List Γ)
    (out : List S) (a : S) (g : Γ) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++ (false,g)::remaining.map (false,·))
    (ha : anchorView cells = out.map some ++ none :: List.replicate n none)
    (hg : g ≠ A.blank) (hg' : A.output g = some a) :
    ∃ cells', ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨[],.scan .readout,cells',true,true⟩ ∧
      workView cells' = (done ++ [g]).map (true,·) ++ remaining.map (false,·) ∧
      anchorView cells' = (out ++ [a]).map some ++ List.replicate n none := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,hr⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) (remaining.map (false,·)) hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  let t' : Tag S Γ := {t with outputRead := true}
  let mid := p ++ (.workspace,t')::r
  have hs := scan_update A M .readout (.put a) p r .workspace t t'
    (readout_pass A M p done hp) (by simp [cell, ht.1, ht.2, hg, hg', t'])
  rw [← hc] at hs
  have hwm : workView mid = (done ++ [g]).map (true,·) ++ remaining.map (false,·) := by
    simp only [mid, workView_append]
    change workView p ++ (true,t.work)::workView r = _
    change workView p = _ at hp
    change workView r = _ at hr
    simp [hp, hr, ht.2, List.append_assoc]
  have ham : anchorView mid = anchorView cells := by
    rw [hc]
    simp [mid, anchorView, List.filterMap_append]
  obtain ⟨p₂,⟨b₂,t₂⟩,r₂,hc₂,hp₂,hb₂,hr₂⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .anchor _ => some c.2.output | _ => none)
    mid (out.map some) none (List.replicate n none) (ham.trans ha)
  cases b₂ <;> simp only at hb₂
  all_goals try contradiction
  rename_i a₂
  have ht₂ : t₂.output = none := Option.some.inj hb₂
  let t₂' : Tag S Γ := {t₂ with output := some a}
  let result := p₂ ++ (.anchor a₂,t₂')::r₂
  have hs₂ := scan_update A M (.put a) .readout p₂ r₂ (.anchor a₂) t₂ t₂'
    (put_pass A M a p₂ out hp₂) (by simp [cell, ht₂, t₂'])
  rw [← hc₂] at hs₂
  refine ⟨result,hs.trans hs₂,?_,?_⟩
  · have heq : workView result = workView mid := by
      rw [hc₂]
      simp [result, workView, List.filterMap_append]
    exact heq.trans hwm
  · simp only [result, anchorView_append]
    change anchorView p₂ ++ some a :: anchorView r₂ = _
    change anchorView p₂ = _ at hp₂
    change anchorView r₂ = _ at hr₂
    simp [hp₂,hr₂,List.append_assoc]

/-- The first unread blank ends output. No cell is changed by the final sweep. -/
theorem readout_blank (cells : Cells S Γ) (done : List Γ) (rest : List (Bool × Γ))
    (hw : workView cells = done.map (true,·) ++ (false,A.blank)::rest) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨cells.reverse,.ok,[],true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,A.blank) rest hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = A.blank := by simpa using hb
  have h₀ := Scan.cross_right (table A M) (.scan .readout) rfl p [] ((.workspace,t)::r)
    true true (readout_pass A M p done hp)
  simp only [List.append_nil] at h₀
  have h₁ : Scan.Step (table A M) ⟨p.reverse,.scan .readout,(.workspace,t)::r,true,true⟩
      ⟨p.reverse,.finish,(.workspace,t)::r,true,true⟩ := by
    simp [Scan.Step, Scan.step, table, cell, ht.1, ht.2]
  have h₂ := finish A M p.reverse ((.workspace,t)::r) true
  simpa [hc, List.reverse_append] using h₀.trans ((ReflTransGen.single h₁).trans h₂)

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

omit [DecidableEq Γ] in
theorem input_ne_blank (a : S) : A.input a ≠ A.blank := by
  intro h
  have := A.output_input a
  rw [h, A.output_blank] at this
  contradiction

/-- Complete readout of a finite, blank-delimited returned string. The spare
    anchor count drops by exactly one for each letter, including when that
    letter's anchor is on the other side of the workspace. -/
theorem readout_complete (out : List S) (cells : Cells S Γ) (done tail : List Γ)
    (old : List S) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++
      (out.map A.input ++ A.blank::tail).map (false,·))
    (ha : anchorView cells = old.map some ++ List.replicate (out.length+n) none) :
    ∃ cells', ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨cells'.reverse,.ok,[],true,true⟩ ∧
      anchorView cells' = (old ++ out).map some ++ List.replicate n none := by
  induction out generalizing cells done old with
  | nil =>
      refine ⟨cells,readout_blank A M cells done (tail.map (false,·)) ?_,?_⟩
      · simpa using hw
      · simpa using ha
  | cons a out ih =>
      have hw' : workView cells = done.map (true,·) ++ (false,A.input a)::
          (out.map A.input ++ A.blank::tail).map (false,·) := by simpa using hw
      have ha' : anchorView cells = old.map some ++ none::
          List.replicate (out.length+n) none := by
        have hn : (a :: out).length + n = (out.length + n) + 1 := by simp; omega
        rw [hn, List.replicate_succ] at ha
        exact ha
      obtain ⟨mid,hs,hmw,hma⟩ := readout_one A M cells done
        (out.map A.input ++ A.blank::tail) old a (A.input a) (out.length+n)
        hw' ha' (input_ne_blank A a) (A.output_input a)
      obtain ⟨result,hr,hra⟩ := ih mid (done ++ [A.input a]) (old ++ [a]) hmw hma
      refine ⟨result,hs.trans hr,?_⟩
      simpa [List.append_assoc] using hra

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- Rejection here means the actual finite table has no forward accepting
    trace; it is stronger than merely failing a chosen simulation trace. -/
def Rejects (v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) : Prop :=
  ∀ w, ReflTransGen (Scan.Step (table A M)) v w → w.head ≠ .ok

theorem terminal_of_none {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : Scan.step (table A M) v = none) : Terminal (Scan.Step (table A M)) v := by
  intro w hw
  rw [Scan.Step, h] at hw
  contradiction

theorem rejects_of_stuck {v s : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hvs : ReflTransGen (Scan.Step (table A M)) v s)
    (hs : Scan.step (table A M) s = none) (hq : s.head ≠ .ok) : Rejects A M v := by
  intro w hw hq'
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic (table A M)) hvs hw with h | h
  · exact hq ((congrArg Scan.Sector.head (terminal_eq_of_reaches (terminal_of_none A M hs) h)).trans hq')
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq')) h
    exact hq ((congrArg Scan.Sector.head he).symm.trans hq')

theorem rejects_before {v s : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hvs : ReflTransGen (Scan.Step (table A M)) v s) (hs : Rejects A M s) : Rejects A M v := by
  intro w hw hq
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic (table A M)) hvs hw with h | h
  · exact hs w h hq
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq)) h
    exact hs s .refl ((congrArg Scan.Sector.head he).symm.trans hq)

/-- No unread cell, in particular no blank delimiter, means that readout stops
    at omega without entering the finish phase. -/
theorem readout_no_unread (cells : Cells S Γ) (done : List Γ)
    (h : workView cells = done.map (true,·)) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan .readout) rfl cells [] [] true true
    (readout_pass A M cells done h)
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by simp [Scan.step,table]) (by simp)

/-- Filled anchors cannot be overwritten. Exhausting them rejects even if a
    workspace character was successfully decoded. -/
theorem put_no_anchor (cells : Cells S Γ) (old : List S) (a : S)
    (h : anchorView cells = old.map some) :
    Rejects A M ⟨[],.scan (.put a),cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan (.put a)) rfl cells [] [] true true
    (put_pass A M a cells old h)
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by simp [Scan.step,table]) (by simp)

/-- Metasymbols that are neither blank nor returned letters block output. -/
theorem readout_invalid (cells : Cells S Γ) (done : List Γ) (g : Γ)
    (rest : List (Bool × Γ))
    (h : workView cells = done.map (true,·) ++ (false,g)::rest)
    (hg : g ≠ A.blank) (hdecode : A.output g = none) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) rest h
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  have hr := Scan.cross_right (table A M) (.scan .readout) rfl p [] ((.workspace,t)::r)
    true true (readout_pass A M p done hp)
  simp only [List.append_nil] at hr
  rw [← hc] at hr
  exact rejects_of_stuck A M hr
    (by simp [Scan.step,table,cell,ht.1,ht.2,hg,hdecode]) (by simp)

/-- The first nonblank output symbol cannot succeed when all anchors are full. -/
theorem readout_no_anchor (cells : Cells S Γ) (done : List Γ) (rest : List (Bool × Γ))
    (old : List S) (a : S) (g : Γ)
    (hw : workView cells = done.map (true,·) ++ (false,g)::rest)
    (ha : anchorView cells = old.map some)
    (hg : g ≠ A.blank) (hdecode : A.output g = some a) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) rest hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  let t' : Tag S Γ := {t with outputRead := true}
  have hr := scan_update A M .readout (.put a) p r .workspace t t'
    (readout_pass A M p done hp) (by simp [cell,ht.1,ht.2,hg,hdecode,t'])
  rw [← hc] at hr
  apply rejects_before A M hr
  apply put_no_anchor A M (p ++ (.workspace,t')::r) old a
  rw [hc] at ha
  simpa [anchorView,List.filterMap_append] using ha

/-- Insufficient *anchor* quota is rejected without truncating the returned
    string or replacing it by an arbitrary shorter result. -/
theorem readout_too_long (out : List S) (cells : Cells S Γ) (done tail : List Γ)
    (old : List S) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++
      (out.map A.input ++ A.blank::tail).map (false,·))
    (ha : anchorView cells = old.map some ++ List.replicate n none)
    (hn : n < out.length) : Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  induction out generalizing cells done old n with
  | nil => simp at hn
  | cons a out ih =>
      have hw' : workView cells = done.map (true,·) ++ (false,A.input a)::
          (out.map A.input ++ A.blank::tail).map (false,·) := by simpa using hw
      cases n with
      | zero =>
          apply readout_no_anchor A M cells done _ old a (A.input a) hw'
          · simpa using ha
          · exact input_ne_blank A a
          · exact A.output_input a
      | succ n =>
          obtain ⟨mid,hs,hmw,hma⟩ := readout_one A M cells done
            (out.map A.input ++ A.blank::tail) old a (A.input a) n
            hw' ha (input_ne_blank A a) (A.output_input a)
          exact rejects_before A M hs (ih mid (done ++ [A.input a]) (old ++ [a]) n hmw hma
            (by simpa using hn))

end

section
open Relation
variable {S Γ Q : Type*}

/-- Appending untouched blank cells reserves quota without altering any already
    represented tape position. -/
def pad (A : Alphabet S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) : Tape (S := S) (Γ := Γ) (Q := Q) :=
  { c with right := c.right ++ List.replicate n (clean A.blank) }

/-- Unbounded left-ended tape semantics. A cell beyond the finite represented
    region is blank; it is materialized only when reached. No output fact or
    acceptance relation is built into these transition constructors. -/
inductive UnboundedStep (A : Alphabet S Γ) (M : Machine Q Γ) :
    Tape (S := S) (Γ := Γ) (Q := Q) → Tape (S := S) (Γ := Γ) (Q := Q) → Prop
  | within {c d} (h : TapeStep M c d) : UnboundedStep A M c d
  | extend {q l d} (h : TapeStep M ⟨q,l,[clean A.blank]⟩ d) :
      UnboundedStep A M ⟨q,l,[]⟩ d

variable (A : Alphabet S Γ) (M : Machine Q Γ)

/-- A bounded operation never inspects cells beyond its current head and is
    therefore preserved by appending arbitrary extra blank quota. -/
theorem tapeStep_pad {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : TapeStep M c d) (n : ℕ) : TapeStep M (pad A c n) (pad A d n) := by
  cases h with
  | stay h hm => exact .stay h hm
  | right h hm => exact .right h hm
  | leftEdge h hm => exact .leftEdge h hm
  | left h hm => exact .left h hm

theorem tapeRun_pad {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : ReflTransGen (TapeStep M) c d) (n : ℕ) :
    ReflTransGen (TapeStep M) (pad A c n) (pad A d n) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (tapeStep_pad A M hs n)

/-- Every finite unbounded trace uses a finite quota. The terminal padding can
    be prescribed in advance, in particular ensuring an explicit spare blank. -/
theorem finite_quota {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : ReflTransGen (UnboundedStep A M) c d) :
    ∀ n, ∃ k, n ≤ k ∧ ReflTransGen (TapeStep M) (pad A c k) (pad A d n) := by
  induction h with
  | refl => exact fun n => ⟨n,le_rfl,.refl⟩
  | @tail d e _ hs ih =>
      intro n
      cases hs with
      | within hh =>
          obtain ⟨k,hkn,hk⟩ := ih n
          exact ⟨k,hkn,hk.tail (tapeStep_pad A M hh n)⟩
      | @extend q l e hh =>
          obtain ⟨k,hkn,hk⟩ := ih (n+1)
          refine ⟨k,by omega,hk.tail ?_⟩
          simpa [pad,List.replicate_succ] using tapeStep_pad A M hh n

/-- A predicate on full tags insensitive to changes of the work symbol is an
    invariant of every bounded run, not just of a chosen clean execution. -/
theorem tapeStep_tags (P : Tag S Γ → Prop)
    (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : TapeStep M c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  cases h <;> simp only [List.mem_append,List.mem_cons] at hc ⊢
  all_goals
    intro t ht
    rcases ht with (ht | ht)
    · try {exact hc t (Or.inl ht)}
      try {rcases ht with rfl | ht
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inl ht)}
      try {exact hc t (Or.inl (Or.inr ht))}
    · try {rcases ht with rfl | ht
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inr (Or.inr ht))}
      try {exact hc t (Or.inr (Or.inr ht))}
      try {rcases ht with rfl | rfl | ht
           · exact hc _ (Or.inl (Or.inl rfl))
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inr (Or.inr ht))}

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ)

theorem unboundedStep_tags (P : Tag S Γ → Prop)
    (hblank : P (clean A.blank)) (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : UnboundedStep A M c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  cases h with
  | within h => exact tapeStep_tags M P hwrite h hc
  | extend h =>
      apply tapeStep_tags M P hwrite h
      simpa using (show ∀ t, t ∈ _ ∨ t = clean A.blank → P t from
        fun t ht => ht.elim (fun ht => hc t (by simpa using ht)) (fun ht => ht ▸ hblank))

theorem unboundedRun_tags (P : Tag S Γ → Prop)
    (hblank : P (clean A.blank)) (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (UnboundedStep A M) c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact unboundedStep_tags A M P hblank hwrite hs ih

/-- Initial finite representation after copying, before adding blank quota. -/
def initialTape (w : List S) : Tape (S := S) (Γ := Γ) (Q := Q) :=
  ⟨M.initial,[],w.map fun a => (filledWork A a).2⟩

/-- The halt test includes the implicit blank at the first unrepresented cell. -/
def Halted (c : Tape (S := S) (Γ := Γ) (Q := Q)) : Prop :=
  M.transition c.state (c.right.headD (clean A.blank)).work = none

/-- The returned string begins at position zero and is delimited by its first
    blank. Extra blanks may lie outside the finite represented portion. -/
def Returns (c : Tape (S := S) (Γ := Γ) (Q := Q)) (out : List S) : Prop :=
  ∃ n tail, (c.left.reverse ++ c.right).map Tag.work ++ List.replicate n A.blank =
    out.map A.input ++ A.blank::tail

@[simp] theorem pad_left (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    (pad A c n).left = c.left := rfl

@[simp] theorem pad_right (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    (pad A c n).right = c.right ++ List.replicate n (clean A.blank) := rfl

theorem halt_pad {c : Tape (S := S) (Γ := Γ) (Q := Q)} (hc : Halted A M c) (n : ℕ) :
    ∃ t r, (pad A c (n+1)).right = t::r ∧ M.transition c.state t.work = none := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil => exact ⟨clean A.blank,List.replicate n (clean A.blank),rfl,hc⟩
  | cons t r => exact ⟨t,r ++ List.replicate (n+1) (clean A.blank),rfl,hc⟩

theorem workView_workCells (ts : List (Tag S Γ)) :
    workView (workCells ts) = ts.map fun t => (t.outputRead,t.work) := by
  simp [workCells,workView,List.filterMap_map]

@[simp] theorem anchorView_workCells (ts : List (Tag S Γ)) :
    anchorView (workCells ts) = [] := by simp [workCells,anchorView,List.filterMap_map]

/-- Full cell list at readout, with the copied anchors on either side. -/
def finalCells (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) : Cells S Γ :=
  x.map (readAnchor A · true) ++ [bare A .cutC] ++
    workCells (c.left.reverse ++ c.right) ++ bare A .cutD :: y.map (readAnchor A · true)

@[simp] theorem anchorView_readAnchors (xs : List S) (r : Bool) :
    anchorView (xs.map (readAnchor A · r)) = List.replicate xs.length none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change none :: anchorView (xs.map (readAnchor A · r)) = _
      rw [ih]
      rfl

@[simp] theorem workView_readAnchors (xs : List S) (r : Bool) :
    workView (xs.map (readAnchor A · r)) = [] := by
  simp [workView,readAnchor,List.filterMap_map]

theorem finalCells_anchors (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    anchorView (finalCells A x y c) = List.replicate (x.length+y.length) none := by
  have hC : anchorView [bare A .cutC] = [] := rfl
  have hD : anchorView (bare A .cutD :: y.map (readAnchor A · true)) =
      List.replicate y.length none := anchorView_readAnchors A y true
  simp only [finalCells,anchorView_append,anchorView_readAnchors,anchorView_workCells,hC,hD]
  simp

theorem finalCells_work (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hc : ∀ t ∈ c.left ++ c.right, t.outputRead = false) :
    workView (finalCells A x y c) = ((c.left.reverse ++ c.right).map Tag.work).map (false,·) := by
  have hm : (c.left.reverse ++ c.right).map (fun t => (t.outputRead,t.work)) =
      (c.left.reverse ++ c.right).map (fun t => (false,t.work)) := by
    apply List.map_congr_left
    intro t ht
    have : t.outputRead = false := hc t (by simpa using ht)
    rw [this]
  simpa [finalCells,workView_append,workView,bare,List.filterMap_append,List.filterMap_map,
    workCells,readAnchor,List.map_map,Function.comp_def] using hm

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem copy_correct_pad (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩
      (runSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true))
        (pad A (initialTape A M (x++y)) (n+1))) := by
  convert copy_correct A M x y n using 1
  simp [runSector,initialTape,pad,workCells,filledWork,bare,List.map_map,
      Function.comp_def,List.append_assoc]
  rfl

theorem halt_readout_pad (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hc : Halted A M c) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      (runSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true)) (pad A c (n+1)))
      ⟨[],.scan .readout,finalCells A x y (pad A c (n+1)),true,true⟩ := by
  obtain ⟨t,r,hr,hh⟩ := halt_pad A M hc n
  have he : pad A c (n+1) = ⟨c.state,c.left,t::r⟩ := by
    cases c
    simp only [pad] at hr ⊢
    rw [hr]
  rw [he]
  exact halt_readout A M _ _ _ _ _ _ hh

omit [DecidableEq Γ] in
theorem unread_pad (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ)
    (hc : ∀ t ∈ c.left ++ c.right, t.outputRead = false) :
    ∀ t ∈ (pad A c n).left ++ (pad A c n).right, t.outputRead = false := by
  intro t ht
  simp only [pad_left,pad_right,List.mem_append,List.mem_replicate] at ht
  rcases ht with ht | ht | ⟨_,rfl⟩
  · exact hc t (List.mem_append_left _ ht)
  · exact hc t (List.mem_append_right _ ht)
  · rfl

/-- Adequate quota for every genuinely halting, length-bounded output. This
    connects the actual copy/run/readout table, including empty inputs, without
    assuming a bound on the machine's running time or workspace beforehand. -/
theorem simulation_complete (x y out : List S)
    (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (UnboundedStep A M) (initialTape A M (x++y)) c)
    (hhalt : Halted A M c) (hout : Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    ∃ s cells', ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩
      ⟨cells'.reverse,.ok,[],true,true⟩ ∧
      anchorView cells' = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  obtain ⟨n,tail,ho⟩ := hout
  obtain ⟨k,hk,hb⟩ := finite_quota A M hrun (n+1)
  cases k with
  | zero => omega
  | succ k =>
    have hi : ∀ t ∈ (initialTape A M (x++y)).left ++ (initialTape A M (x++y)).right,
        t.outputRead = false := by
      intro t ht
      simp only [initialTape,List.nil_append,List.mem_map] at ht
      obtain ⟨a,_,rfl⟩ := ht
      rfl
    have hc := unboundedRun_tags A M (fun t => t.outputRead = false) rfl
      (fun _ _ ht => ht) hrun hi
    have hwork := finalCells_work A x y (pad A c (n+1)) (unread_pad A c (n+1) hc)
    have he : ((pad A c (n+1)).left.reverse ++ (pad A c (n+1)).right).map Tag.work =
        out.map A.input ++ A.blank::(tail ++ [A.blank]) := by
      simpa [pad,List.map_append,List.map_replicate,clean,List.replicate_succ',
        List.append_assoc] using congrArg (· ++ [A.blank]) ho
    rw [he] at hwork
    have ha : anchorView (finalCells A x y (pad A c (n+1))) =
        ([] : List S).map some ++ List.replicate
          (out.length + (x.length+y.length-out.length)) none := by
      have hn : out.length + (x.length+y.length-out.length) = x.length+y.length := by omega
      simpa [hn] using finalCells_anchors A x y (pad A c (n+1))
    obtain ⟨cells',hr,ha'⟩ := readout_complete A M out (finalCells A x y (pad A c (n+1)))
      [] (tail ++ [A.blank]) [] (x.length+y.length-out.length) (by simpa using hwork) ha
    refine ⟨x.length+y.length+k+1,cells',?_,by simpa using ha'⟩
    exact (copy_correct_pad A M x y k).trans
      ((tapeRun_simulates A M _ _ hb).trans ((halt_readout_pad A M x y c hhalt n).trans hr))

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- The first readout-rewind configuration, before any tape cell is moved. -/
def haltSector (x y : Cells S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    Scan.Sector (Head S Q) (Base S) (Tag S Γ) :=
  ⟨workCells c.left ++ bare A .cutC :: x.reverse, .rewind .readout,
    workCells c.right ++ bare A .cutD :: y,true,true⟩

/-- Exact classification of a simulator step made in a workspace run phase.
    The only intermediate phase is the deterministic half of a left move. -/
theorem run_step_cases (x y : Cells S Γ)
    (c : Tape (S := S) (Γ := Γ) (Q := Q))
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : Scan.Step (table A M) (runSector A x y c) v) :
    (∃ d, TapeStep M c d ∧ (v = runSector A x y d ∨
      ((∃ q, v.head = .left q) ∧ Scan.Step (table A M) v (runSector A x y d)))) ∨
    (Halted A M c ∧ v = haltSector A x y c) := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil => simp [Scan.Step,quota_exhausted] at h
  | cons t r =>
      cases hc : M.transition q t.work with
      | none =>
          right
          constructor
          · exact hc
          · simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,haltSector] using h.symm
      | some d =>
          left
          cases hm : d.move with
          | stay =>
              refine ⟨⟨d.state,l,writeWork t d.write::r⟩,.stay hc hm,Or.inl ?_⟩
              simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
          | right =>
              refine ⟨⟨d.state,writeWork t d.write::l,r⟩,.right hc hm,Or.inl ?_⟩
              simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
          | left =>
              have hv : v =
                  ⟨workCells l ++ bare A .cutC :: x.reverse, .left d.state,
                    (.workspace,writeWork t d.write) :: (workCells r ++ bare A .cutD :: y),
                    true,true⟩ := by
                simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
              subst v
              cases l with
              | nil =>
                  refine ⟨⟨d.state,[],writeWork t d.write::r⟩,.leftEdge hc hm,
                    Or.inr ⟨⟨d.state,rfl⟩,?_⟩⟩
                  simp [Scan.Step,Scan.step,table,cell,runSector,workCells,bare]
              | cons a l =>
                  refine ⟨⟨d.state,l,a::writeWork t d.write::r⟩,.left hc hm,
                    Or.inr ⟨⟨d.state,rfl⟩,?_⟩⟩
                  simp [Scan.Step,Scan.step,table,cell,runSector,workCells]

/-- Arbitrary accepting paths, not just chosen forward simulations, must have
    exited the run phases through a genuine in-bounds machine halt. -/
theorem simulation_halt_sound (x y : Cells S Γ)
    {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : ReflTransGen (Scan.Step (table A M)) (runSector A x y c) v)
    (hv : v.head = .ok) :
    ∃ d, ReflTransGen (TapeStep M) c d ∧ Halted A M d ∧
      ReflTransGen (Scan.Step (table A M)) (haltSector A x y d) v := by
  have hi :
      (∃ d, ReflTransGen (TapeStep M) c d ∧ v = runSector A x y d) ∨
      (∃ d, ReflTransGen (TapeStep M) c d ∧ (∃ q, v.head = .left q) ∧
        Scan.Step (table A M) v (runSector A x y d)) ∨
      (∃ d, ReflTransGen (TapeStep M) c d ∧ Halted A M d ∧
        ReflTransGen (Scan.Step (table A M)) (haltSector A x y d) v) := by
    clear hv
    induction h with
    | refl => exact Or.inl ⟨c,.refl,rfl⟩
    | @tail v w hpre hs ih =>
        rcases ih with ⟨d,hd,rfl⟩ | ⟨d,hd,_,hf⟩ | ⟨d,hd,hh,hr⟩
        · rcases run_step_cases A M x y d hs with ⟨e,hde,he | ⟨hq,he⟩⟩ | ⟨hh,he⟩
          · exact Or.inl ⟨e,hd.tail hde,he⟩
          · exact Or.inr (Or.inl ⟨e,hd.tail hde,hq,he⟩)
          · exact Or.inr (Or.inr ⟨d,hd,hh,he ▸ ReflTransGen.refl⟩)
        · exact Or.inl ⟨d,hd,Scan.deterministic _ hs hf⟩
        · exact Or.inr (Or.inr ⟨d,hd,hh,hr.tail hs⟩)
  rcases hi with ⟨d,_,hd⟩ | ⟨d,_,⟨q,hq⟩,_⟩ | hgood
  · simp [hd,runSector] at hv
  · simp [hq] at hv
  · exact hgood

end

section
open Relation
variable {S Γ Q : Type*}

/-- Semantic one-sided tape: its right end is an infinite blank tail, not an
    extra halting edge. Auxiliary simulator tags do not enter this semantics. -/
structure SemanticTape (Γ Q : Type*) where
  state : Q
  left : List Γ
  right : Stream' Γ

/-- The literal machine command interpreted on an infinite right-hand tape. -/
def semanticStep (M : Machine Q Γ) (c : SemanticTape Γ Q) : Option (SemanticTape Γ Q) :=
  (M.transition c.state c.right.head).map fun d =>
    match d.move with
    | .stay => ⟨d.state,c.left,Stream'.cons d.write c.right.tail⟩
    | .right => ⟨d.state,d.write::c.left,c.right.tail⟩
    | .left => match c.left with
      | [] => ⟨d.state,[],Stream'.cons d.write c.right.tail⟩
      | a::l => ⟨d.state,l,Stream'.cons a (Stream'.cons d.write c.right.tail)⟩

def SemanticStep (M : Machine Q Γ) (c d : SemanticTape Γ Q) : Prop :=
  semanticStep M c = some d

def interpret (A : Alphabet S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) : SemanticTape Γ Q :=
  ⟨c.state,c.left.map Tag.work,
    Stream'.appendStream' (c.right.map Tag.work) (Stream'.const A.blank)⟩

theorem replicate_append_const (b : Γ) (n : ℕ) :
    Stream'.appendStream' (List.replicate n b) (Stream'.const b) = Stream'.const b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ,Stream'.appendStream',ih]
      exact (Stream'.const_eq b).symm

@[simp] theorem interpret_pad (A : Alphabet S Γ)
    (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    interpret A (pad A c n) = interpret A c := by
  rcases c with ⟨q,l,r⟩
  simp [interpret,pad,List.map_append,List.map_replicate,clean,replicate_append_const]

/-- Each bounded transition is exactly one transition of the semantic machine. -/
theorem tapeStep_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : TapeStep M c d) :
    SemanticStep M (interpret A c) (interpret A d) := by
  cases h <;>
    simp_all [SemanticStep,semanticStep,interpret,Stream'.appendStream',writeWork]

/-- Materializing an implicit blank never changes the semantic tape. -/
theorem unboundedStep_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : UnboundedStep A M c d) :
    SemanticStep M (interpret A c) (interpret A d) := by
  cases h with
  | within h => exact tapeStep_interpret A M h
  | @extend q l d h =>
      have hi : interpret A (⟨q,l,[clean A.blank]⟩ : Tape (S := S) (Γ := Γ) (Q := Q)) =
          interpret A (⟨q,l,[]⟩ : Tape (S := S) (Γ := Γ) (Q := Q)) := by
        exact interpret_pad A ⟨q,l,[]⟩ 1
      rw [← hi]
      exact tapeStep_interpret A M h

theorem tapeRun_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (TapeStep M) c d) :
    ReflTransGen (SemanticStep M) (interpret A c) (interpret A d) :=
  h.lift (interpret A) (fun _ _ => tapeStep_interpret A M)

theorem unboundedRun_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (UnboundedStep A M) c d) :
    ReflTransGen (SemanticStep M) (interpret A c) (interpret A d) :=
  h.lift (interpret A) (fun _ _ => unboundedStep_interpret A M)

theorem semantic_deterministic (M : Machine Q Γ) : Relator.RightUnique (SemanticStep M) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

theorem halted_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c : Tape (S := S) (Γ := Γ) (Q := Q)} (h : Halted A M c) :
    Terminal (SemanticStep M) (interpret A c) := by
  intro d hd
  rcases c with ⟨q,l,r⟩
  cases r <;> simp_all [Halted,SemanticStep,semanticStep,interpret,
    Stream'.appendStream',clean,Stream'.head,Stream'.get,Stream'.const,Stream'.cons]

/-- Halts with different finite quotas represent the same semantic output.
    In particular a workspace edge can neither invent a halt nor alter one. -/
theorem halted_quota_unique (A : Alphabet S Γ) (M : Machine Q Γ)
    {start c d : Tape (S := S) (Γ := Γ) (Q := Q)} (n : ℕ)
    (hc : ReflTransGen (TapeStep M) (pad A start n) c)
    (hd : ReflTransGen (UnboundedStep A M) start d)
    (hhc : Halted A M c) (hhd : Halted A M d) : interpret A c = interpret A d := by
  have hci := tapeRun_interpret A M hc
  rw [interpret_pad] at hci
  have hdi := unboundedRun_interpret A M hd
  rcases ReflTransGen.total_of_right_unique (semantic_deterministic M) hci hdi with h | h
  · exact terminal_eq_of_reaches (halted_interpret A M hhc) h
  · exact (terminal_eq_of_reaches (halted_interpret A M hhd) h).symm

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- An accepting terminal cannot be bypassed by any other finite forward path. -/
theorem accepting_after
    {v s w : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hs : ReflTransGen (Scan.Step (table A M)) v s)
    (hw : ReflTransGen (Scan.Step (table A M)) v w) (hq : w.head = .ok) :
    ReflTransGen (Scan.Step (table A M)) s w := by
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic _) hs hw with h | h
  · exact h
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq)) h
    exact he ▸ ReflTransGen.refl

/-- Soundness of the output scans, under the literal decoding convention of
    the compiled alphabet. Both the first blank and the anchor quota are forced;
    the result is not an arbitrary truncation of a workspace string. -/
theorem readout_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (remaining : List Γ) (cells : Cells S Γ) (done : List Γ) (old : List S) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++ remaining.map (false,·))
    (ha : anchorView cells = old.map some ++ List.replicate n none)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M)) ⟨[],.scan .readout,cells,true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ out tail result, remaining = out.map A.input ++ A.blank::tail ∧ out.length ≤ n ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = (old ++ out).map some ++ List.replicate (n-out.length) none := by
  induction remaining generalizing cells done old n with
  | nil =>
      have hr := readout_no_unread A M cells done (by simpa using hw)
      exact False.elim (hr v hv hq)
  | cons g remaining ih =>
      by_cases hg : g = A.blank
      · subst g
        have hr := readout_blank A M cells done (remaining.map (false,·)) (by simpa using hw)
        have he := terminal_eq_of_reaches (terminal_of_none A M
          (ok_terminal A M ⟨cells.reverse,.ok,[],true,true⟩ rfl))
          (accepting_after A M hr hv hq)
        exact ⟨[],remaining,cells,rfl,Nat.zero_le _,he.symm,by simpa using ha⟩
      · cases hg' : A.output g with
        | none =>
            exact False.elim ((readout_invalid A M cells done g (remaining.map (false,·))
              (by simpa using hw) hg hg') v hv hq)
        | some a =>
            cases n with
            | zero =>
                exact False.elim ((readout_no_anchor A M cells done (remaining.map (false,·)) old a g
                  (by simpa using hw) (by simpa using ha) hg hg') v hv hq)
            | succ n =>
                obtain ⟨cells',hr,hw',ha'⟩ := readout_one A M cells done remaining old a g n
                  (by simpa using hw) (by simpa only [List.replicate_succ] using ha) hg hg'
                obtain ⟨out,tail,result,hout,hlen,he,haout⟩ := ih cells' (done ++ [g])
                  (old ++ [a]) n hw' ha' (accepting_after A M hr hv hq)
                refine ⟨a::out,tail,result,?_,by simpa using Nat.succ_le_succ hlen,he,?_⟩
                · simp [hdecode g a hg',hout]
                · simpa [List.append_assoc] using haout

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ)

/-- The whole semantic tape, read in physical order starting at cell zero. -/
def semanticContent (c : SemanticTape Γ Q) : Stream' Γ :=
  Stream'.appendStream' c.left.reverse c.right

/-- Standard literal, first-blank-delimited machine output. -/
def SemanticReturns (c : SemanticTape Γ Q) (w : List S) : Prop :=
  ∃ tail, semanticContent c = Stream'.appendStream' (w.map A.input) (Stream'.cons A.blank tail)

theorem returns_interpret {c : Tape (S := S) (Γ := Γ) (Q := Q)} {w : List S}
    (h : Returns A c w) : SemanticReturns A (interpret A c) w := by
  obtain ⟨n,tail,h⟩ := h
  refine ⟨Stream'.appendStream' tail (Stream'.const A.blank),?_⟩
  have hi := congrArg (fun l => Stream'.appendStream' l (Stream'.const A.blank)) h
  simpa [semanticContent,interpret,List.map_append,List.map_reverse,
    Stream'.append_append_stream,replicate_append_const,Stream'.appendStream'] using hi

theorem input_injective : Function.Injective A.input := by
  intro a b h
  have hi := congrArg A.output h
  simpa only [A.output_input,Option.some.injEq] using hi

/-- The input alphabet excludes the delimiter, so two literal returned prefixes
    of the same infinite tape must be the same list, including empty output. -/
theorem delimited_prefix_unique (x y : List S) (r s : Stream' Γ)
    (h : Stream'.appendStream' (x.map A.input) (Stream'.cons A.blank r) =
      Stream'.appendStream' (y.map A.input) (Stream'.cons A.blank s)) : x = y := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => rfl
      | cons b y =>
          have hi := congrArg Stream'.head h
          simp only [List.map_nil,List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          exact False.elim (input_ne_blank A b hi.symm)
  | cons a x ih =>
      cases y with
      | nil =>
          have hi := congrArg Stream'.head h
          simp only [List.map_nil,List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          exact False.elim (input_ne_blank A a hi)
      | cons b y =>
          have hi := congrArg Stream'.head h
          have ht := congrArg Stream'.tail h
          simp only [List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          simp only [List.map_cons,Stream'.appendStream',Stream'.tail_cons] at ht
          exact congrArg₂ List.cons (input_injective A hi) (ih y ht)

theorem semanticReturns_unique {c : SemanticTape Γ Q} {x y : List S}
    (hx : SemanticReturns A c x) (hy : SemanticReturns A c y) : x = y := by
  obtain ⟨r,hr⟩ := hx
  obtain ⟨s,hs⟩ := hy
  exact delimited_prefix_unique A x y r s (hr.symm.trans hs)

/-- The output of any bounded accepting computation agrees with the output of
    a genuine unbounded halt, whenever both are expressed in the literal input
    alphabet. This compares different quotas without comparing their padding. -/
theorem returned_quota_unique (M : Machine Q Γ)
    {start c d : Tape (S := S) (Γ := Γ) (Q := Q)} (n : ℕ)
    (hc : ReflTransGen (TapeStep M) (pad A start n) c)
    (hd : ReflTransGen (UnboundedStep A M) start d)
    (hhc : Halted A M c) (hhd : Halted A M d) {x y : List S}
    (hx : Returns A c x) (hy : Returns A d y) : x = y := by
  have he := halted_quota_unique A M n hc hd hhc hhd
  apply semanticReturns_unique A (returns_interpret A hx)
  rw [he]
  exact returns_interpret A hy

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem haltSector_readout (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    ReflTransGen (Scan.Step (table A M))
      (haltSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true)) c)
      ⟨[],.scan .readout,finalCells A x y c,true,true⟩ := by
  simpa [haltSector,finalCells,workCells,List.reverse_append,List.reverse_cons,
    List.map_reverse,List.append_assoc] using
    (rewind A M .readout
      (workCells c.left ++ bare A .cutC :: (x.map (readAnchor A · true)).reverse)
      (workCells c.right ++ bare A .cutD :: y.map (readAnchor A · true)) true)

omit [DecidableEq Γ] in
theorem tapeRun_tags (P : Tag S Γ → Prop)
    (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (TapeStep M) c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact tapeStep_tags M P hwrite hs ih

/-- Exact soundness from the fresh validated handoff, with a positive spare
    workspace quota. Arbitrary successes are actual halts returning exactly the
    output marks that cleanup will retain. -/
theorem simulation_sound_sufficient
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (x y : List S) (n : ℕ)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ c out result,
      ReflTransGen (TapeStep M) (pad A (initialTape A M (x++y)) (n+1)) c ∧
      Halted A M c ∧ Returns A c out ∧ out.length ≤ x.length+y.length ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  have hrun := accepting_after A M (copy_correct_pad A M x y n) hv hq
  obtain ⟨c,hc,hh,hr⟩ := simulation_halt_sound A M _ _ hrun hq
  have hi : ∀ t ∈ (initialTape A M (x++y)).left ++ (initialTape A M (x++y)).right,
      t.outputRead = false := by
    intro t ht
    simp only [initialTape,List.nil_append,List.mem_map] at ht
    obtain ⟨a,_,rfl⟩ := ht
    rfl
  have hunread := tapeRun_tags M (fun t => t.outputRead = false) (fun _ _ ht => ht)
    hc (unread_pad A _ (n+1) hi)
  have hr' := accepting_after A M (haltSector_readout A M x y c) hr hq
  obtain ⟨out,tail,result,hout,hlen,he,ha⟩ := readout_sound A M hdecode
    ((c.left.reverse ++ c.right).map Tag.work) (finalCells A x y c) [] []
    (x.length+y.length) (by simpa using finalCells_work A x y c hunread)
    (by simpa using finalCells_anchors A x y c) hr' hq
  exact ⟨c,out,result,hc,hh,⟨0,tail,by simpa using hout⟩,hlen,he,by simpa using ha⟩

end

open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

@[simp] theorem pass_fill_bareD (a : S) : Pass A M (.fill a) (bare A .cutD) := by rfl
@[simp] theorem pass_spare_D : Pass A M .spare (bare A .cutD) := by rfl

theorem scan_exhausted (s : Resume S) (cells : Cells S Γ)
    (hp : ∀ c ∈ cells, Pass A M s c) (hb : (table A M).boundary (.scan s) = none) :
    Rejects A M ⟨[],.scan s,cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan s) rfl cells [] [] true true hp
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by
    change ((table A M).boundary (.scan s)).map _ = none
    rw [hb]; rfl) (by simp)

theorem fill_no_space (xp xs yp ys w : List S) (a : S) :
    Rejects A M ⟨[],.scan (.fill a),body A xp xs yp ys w 0,true,true⟩ := by
  apply scan_exhausted A M _ _ _ rfl
  simp only [body,List.replicate_zero,List.append_nil,List.forall_mem_append,
    List.forall_mem_map,List.forall_mem_singleton]
  simp

/-- Zero spare workspace is a genuine rejection even for empty input. -/
theorem copy_no_space (xp xs yp ys w : List S) :
    Rejects A M ⟨[],.scan .input,body A xp xs yp ys w 0,true,true⟩ := by
  cases xs with
  | cons a xs =>
      let p := xp.map (readAnchor A · true)
      let r := xs.map (readAnchor A · false) ++ [bare A .cutC] ++ w.map (filledWork A) ++
        [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
      have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
        (readAnchor A a false).2 (readAnchor A a true).2
        (by change ∀ c ∈ p, Pass A M .input c; simp [p]) (by rfl)
      have hr : ReflTransGen (Scan.Step (table A M))
          ⟨[],.scan .input,body A xp (a::xs) yp ys w 0,true,true⟩
          ⟨[],.scan (.fill a),body A (xp++[a]) xs yp ys w 0,true,true⟩ := by
        simpa [body,p,r,readAnchor,List.append_assoc] using h₁
      exact rejects_before A M hr (fill_no_space A M _ _ _ _ _ a)
  | nil =>
      cases ys with
      | cons a ys =>
          let p := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A) ++
            [bare A .cutD] ++ yp.map (readAnchor A · true)
          let r := ys.map (readAnchor A · false)
          have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
            (readAnchor A a false).2 (readAnchor A a true).2
            (by
              change ∀ c ∈ p, Pass A M .input c
              simp only [p,List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
              simp) (by rfl)
          have hr : ReflTransGen (Scan.Step (table A M))
              ⟨[],.scan .input,body A xp [] yp (a::ys) w 0,true,true⟩
              ⟨[],.scan (.fill a),body A xp [] (yp++[a]) ys w 0,true,true⟩ := by
            simpa [body,p,r,readAnchor,List.append_assoc] using h₁
          exact rejects_before A M hr (fill_no_space A M _ _ _ _ _ a)
      | nil =>
          let cells := body A xp [] yp [] w 0
          have hp : ∀ c ∈ cells, Pass A M .input c := by
            simp only [cells,body,List.map_nil,List.replicate_zero,List.append_nil,
              List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
            simp
          have h₀ := Scan.cross_right (table A M) (.scan .input) rfl cells [] [] true true hp
          have h₁ : Scan.Step (table A M) ⟨cells.reverse,.scan .input,[],true,true⟩
              ⟨cells.reverse,.rewind .spare,[],true,true⟩ := by
            simp [Scan.Step,Scan.step,table]
          have h₂ := rewind A M .spare cells.reverse [] true
          simp only [List.reverse_reverse,List.append_nil] at h₀ h₂
          apply rejects_before A M (h₀.trans ((ReflTransGen.single h₁).trans h₂))
          apply scan_exhausted A M _ _ _ rfl
          simp only [cells,body,List.map_nil,List.replicate_zero,List.append_nil,
            List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
          simp

/-- A quota no larger than the unread input rejects: there must be space for
    every copied letter and also the spare blank tested before running. -/
theorem copy_insufficient (xp xs yp ys w : List S) (n : ℕ)
    (hn : n ≤ xs.length+ys.length) :
    Rejects A M ⟨[],.scan .input,body A xp xs yp ys w n,true,true⟩ := by
  induction n generalizing xp xs yp ys w with
  | zero => exact copy_no_space A M xp xs yp ys w
  | succ n ih =>
      cases xs with
      | cons a xs =>
          apply rejects_before A M (copy_left_one A M xp xs yp ys w a n)
          exact ih _ _ _ _ _ (by simp only [List.length_cons] at hn ⊢; omega)
      | nil =>
          cases ys with
          | nil => simp at hn
          | cons a ys =>
              apply rejects_before A M (copy_right_one A M xp yp ys w a n)
              exact ih _ _ _ _ _ (by simp only [List.length_cons, List.length_nil] at hn ⊢; omega)

/-- Insufficient quota cannot give an accepting computation from a clean
    post-validator handoff, including the zero-workspace and empty-input cases. -/
theorem simulation_insufficient (x y : List S) (s : ℕ) (hs : s ≤ x.length+y.length) :
    Rejects A M ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩ :=
  rejects_before A M (start_copy A M _) (copy_insufficient A M [] x [] y [] s hs)

/-- Soundness for *every* clean quota, without a promise that enough was
    inserted. All accepting paths return the genuine first-blank-delimited
    machine output, in input order and within the anchor length bound. -/
theorem simulation_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (x y : List S) (s : ℕ)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ n c out result, s = x.length+y.length+n+1 ∧
      ReflTransGen (TapeStep M) (pad A (initialTape A M (x++y)) (n+1)) c ∧
      Halted A M c ∧ Returns A c out ∧ out.length ≤ x.length+y.length ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  by_cases hs : s ≤ x.length+y.length
  · exact False.elim (simulation_insufficient A M x y s hs v hv hq)
  · let n := s - (x.length+y.length+1)
    have he : s = x.length+y.length+n+1 := by dsimp [n]; omega
    rw [he] at hv
    obtain ⟨c,out,result,h⟩ := simulation_sound_sufficient A M hdecode x y n hv hq
    exact ⟨n,c,out,result,he,h⟩

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
