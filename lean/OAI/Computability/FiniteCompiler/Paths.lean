import OAI.Computability.FiniteCompiler.Surface

namespace OAI

/-!
Path alphabet, sectors, cuts, and contextual preparation.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Path

section

inductive Vertex
  | outer | left | right
  deriving DecidableEq

instance : Fintype Vertex := ⟨{.outer,.left,.right}, by intro x; cases x <;> simp⟩

/-- There are no vertex-identity letters. `zero` is the absorbing letter. -/
inductive Letter (C H : Type*)
  | zero | enter | leave
  | head : H → Letter C H
  | left : C → Letter C H
  | right : C → Letter C H
  deriving DecidableEq, Fintype

/-- Boundary type of a word; `unit` belongs only to the empty word. -/
inductive Shape
  | zero | unit
  | path : Vertex → Vertex → Shape
  deriving DecidableEq

instance : Fintype Shape :=
  ⟨{.zero,.unit} ∪ Finset.univ.biUnion (fun a => Finset.univ.image (Shape.path a)), by
    intro x; cases x <;> simp⟩

def Shape.comp : Shape → Shape → Shape
  | .zero,_ => .zero
  | _,.zero => .zero
  | .unit,b => b
  | a,.unit => a
  | .path a b,.path c d => if b = c then .path a d else .zero

instance : Monoid Shape where
  mul := Shape.comp
  one := .unit
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide

@[simp] theorem unit_mul (s : Shape) : Shape.unit * s = s := one_mul s
@[simp] theorem mul_unit (s : Shape) : s * Shape.unit = s := mul_one s

@[simp] theorem zero_mul (s : Shape) : Shape.zero * s = .zero := rfl
@[simp] theorem mul_zero (s : Shape) : s * Shape.zero = .zero := by cases s <;> rfl
@[simp] theorem path_mul_path (a b c d : Vertex) :
    Shape.path a b * Shape.path c d = if b = c then .path a d else .zero := rfl

variable {C H : Type*}

def typeOf : Letter C H → Shape
  | .zero => .zero
  | .enter => .path .outer .left
  | .leave => .path .right .outer
  | .head _ => .path .left .right
  | .left _ => .path .left .left
  | .right _ => .path .right .right

def shape (w : List (Letter C H)) : Shape := (w.map typeOf).prod

@[simp] theorem shape_nil : shape ([] : List (Letter C H)) = .unit := rfl
@[simp] theorem shape_cons (a : Letter C H) (w : List (Letter C H)) :
    shape (a::w) = typeOf a * shape w := by simp [shape]
@[simp] theorem shape_append (u v : List (Letter C H)) :
    shape (u++v) = shape u * shape v := by simp [shape]
@[simp] theorem shape_singleton (a : Letter C H) : shape [a] = typeOf a := by simp

/-- Parallel nonzero equation sides preserve the complete contextual shape,
    including nonpath status. This also covers all length-decreasing cleanup. -/
theorem shape_context {u v : List (Letter C H)} (h : shape u = shape v)
    (x y : List (Letter C H)) : shape (x++u++y) = shape (x++v++y) := by simp [h]

theorem shape_zero_context (x y : List (Letter C H)) :
    shape (x ++ .zero :: y) = .zero := by simp [typeOf]

@[simp] theorem typeOf_ne_unit (a : Letter C H) : typeOf a ≠ .unit := by
  cases a <;> simp [typeOf]

theorem comp_eq_unit_iff : ∀ (a b : Shape), a*b = .unit ↔ a = .unit ∧ b = .unit := by decide

theorem shape_unit_iff (w : List (Letter C H)) : shape w = .unit ↔ w = [] := by
  cases w <;> simp [comp_eq_unit_iff]

/-- A headed sector written literally. Cells left of the head are supplied in
    nearest-first zipper order. -/
def headed (l : List C) (q : H) (r : List C) (lb rb : Bool) : List (Letter C H) :=
  (if lb then [.enter] else []) ++ l.reverse.map .left ++ [.head q] ++
    r.map .right ++ (if rb then [.leave] else [])

@[simp] theorem shape_left (l : List C) :
    shape (l.map (Letter.left : C → Letter C H)) =
      if l = [] then .unit else .path .left .left := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp [typeOf]
    | cons b l => simp_all [typeOf]

@[simp] theorem shape_right (l : List C) :
    shape (l.map (Letter.right : C → Letter C H)) =
      if l = [] then .unit else .path .right .right := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp [typeOf]
    | cons b l => simp_all [typeOf]

@[simp] theorem shape_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    shape (headed l q r lb rb) =
      .path (if lb then .outer else .left) (if rb then .outer else .right) := by
  classical
  unfold headed
  simp only [shape_append,shape_left,shape_right,shape_singleton,List.reverse_eq_nil_iff]
  cases lb <;> cases rb <;> by_cases hl : l = [] <;> by_cases hr : r = [] <;>
    simp [hl,hr,typeOf]

def heads : List (Letter C H) → List H := List.filterMap fun
  | .head q => some q
  | _ => none

def lefts : List (Letter C H) → List C := List.filterMap fun
  | .left c => some c
  | _ => none

def rights : List (Letter C H) → List C := List.filterMap fun
  | .right c => some c
  | _ => none

@[simp] theorem heads_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    heads (headed l q r lb rb) = [q] := by
  cases lb <;> cases rb <;> simp [headed,heads,List.filterMap_map]

@[simp] theorem lefts_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    lefts (headed l q r lb rb) = l.reverse := by
  cases lb <;> cases rb <;> simp [headed,lefts,List.filterMap_map]

@[simp] theorem rights_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    rights (headed l q r lb rb) = r := by
  cases lb <;> cases rb <;> simp [headed,rights,List.filterMap_map]

theorem headed_injective {l l' r r' : List C} {q q' : H} {lb lb' rb rb' : Bool}
    (h : headed l q r lb rb = headed l' q' r' lb' rb') :
    l = l' ∧ q = q' ∧ r = r' ∧ lb = lb' ∧ rb = rb' := by
  have hq := congrArg heads h
  have hl := congrArg lefts h
  have hr := congrArg rights h
  simp only [heads_headed,List.singleton_inj] at hq
  simp only [lefts_headed,List.reverse_inj] at hl
  simp only [rights_headed] at hr
  refine ⟨hl,hq,hr,?_⟩
  have hs := congrArg shape h
  simp only [shape_headed,Shape.path.injEq] at hs
  cases lb <;> cases lb' <;> cases rb <;> cases rb' <;> simp_all

/-- Prefix a (possibly empty) fragment to the first sector, creating a sector
    only when the fragment is nonempty. -/
def glue (u : List (Letter C H)) (cs : List (List (Letter C H))) : List (List (Letter C H)) :=
  match cs with
  | c::cs => (u++c)::cs
  | [] => match u with
    | [] => []
    | _::_ => [u]

@[simp] theorem glue_nil (cs : List (List (Letter C H))) : glue [] cs = cs := by
  cases cs <;> rfl

@[simp] theorem glue_cons (u c : List (Letter C H)) (cs : List (List (Letter C H))) :
    glue u (c::cs) = (u++c)::cs := rfl

theorem glue_assoc (u v : List (Letter C H)) (cs : List (List (Letter C H))) :
    glue u (glue v cs) = glue (u++v) cs := by
  cases cs <;> cases u <;> cases v <;> simp [glue,List.append_assoc]

/-- Cut immediately after an omega, omitting the empty final sector. On paths
    every interior cut is exactly omega-alpha, including headless end sectors. -/
def cuts : List (Letter C H) → List (List (Letter C H))
  | [] => []
  | .leave::w => [.leave] :: cuts w
  | a::w => glue [a] (cuts w)

@[simp] theorem cuts_nil : cuts ([] : List (Letter C H)) = [] := rfl
@[simp] theorem cuts_leave (w : List (Letter C H)) : cuts (.leave::w) = [.leave]::cuts w := rfl

theorem cuts_cons {a : Letter C H} (ha : a ≠ .leave) (w : List (Letter C H)) :
    cuts (a::w) = glue [a] (cuts w) := by cases a <;> simp_all [cuts]

@[simp] theorem flatten_glue (u : List (Letter C H)) (cs : List (List (Letter C H))) :
    (glue u cs).flatten = u ++ cs.flatten := by
  cases cs <;> cases u <;> simp [glue,List.append_assoc]

@[simp] theorem flatten_cuts (w : List (Letter C H)) : (cuts w).flatten = w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [cuts,ih]

theorem glue_singleton_nonempty (a : Letter C H) (cs : List (List (Letter C H)))
    (h : ∀ c ∈ cs, c ≠ []) : ∀ c ∈ glue [a] cs, c ≠ [] := by
  cases cs with
  | nil => simp [glue]
  | cons c cs =>
    simp only [glue,List.cons_append,List.nil_append,List.mem_cons]
    intro d hd
    rcases hd with rfl | hd
    · simp
    · exact h d (List.mem_cons_of_mem _ hd)

theorem cuts_nonempty (w : List (Letter C H)) : ∀ c ∈ cuts w, c ≠ [] := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a <;> simp only [cuts]
    case leave =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp
      · exact ih c hc
    all_goals exact glue_singleton_nonempty _ _ ih

theorem cuts_append_nonleave (u v : List (Letter C H)) (hu : Letter.leave ∉ u) :
    cuts (u++v) = glue u (cuts v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have ha : a ≠ .leave := fun h => hu (by simp [h])
    have hu' : Letter.leave ∉ u := fun h => hu (List.mem_cons_of_mem _ h)
    rw [List.cons_append,cuts_cons ha,ih hu',glue_assoc]
    rfl

theorem cuts_of_noLeave (u : List (Letter C H)) (hu : Letter.leave ∉ u) :
    cuts u = glue u [] := by simpa using cuts_append_nonleave u [] hu

@[simp] theorem headed_ne_nil (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    headed l q r lb rb ≠ [] := by
  intro he
  have hh := congrArg heads he
  rw [heads_headed] at hh
  change [q] = [] at hh
  cases hh

@[simp] theorem cuts_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    cuts (headed l q r lb rb) = [headed l q r lb rb] := by
  have hn : (Letter.leave : Letter C H) ∉ headed l q r lb false := by
    cases lb <;> simp [headed]
  have hne := headed_ne_nil l q r lb false
  cases rb
  · rw [cuts_of_noLeave _ hn]
    cases he : headed l q r lb false with
    | nil => exact (hne he).elim
    | cons a w => rfl
  · have he : headed l q r lb true = headed l q r lb false ++ [.leave] := by
      simp [headed,List.append_assoc]
    rw [he,cuts_append_nonleave _ _ hn]
    rfl

theorem shape_append_ne_zero {u v : List (Letter C H)} (h : shape (u++v) ≠ .zero) :
    shape u ≠ .zero ∧ shape v ≠ .zero := by
  constructor <;> intro hz <;> apply h <;> simp [hz]

theorem shape_mem_flatten_ne_zero {cs : List (List (Letter C H))}
    (h : shape cs.flatten ≠ .zero) {c : List (Letter C H)} (hc : c ∈ cs) : shape c ≠ .zero := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    have hh := shape_append_ne_zero h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hh.1
    · exact ih hh.2 hc

theorem shape_cut_ne_zero {w : List (Letter C H)} (hw : shape w ≠ .zero)
    {c : List (Letter C H)} (hc : c ∈ cuts w) : shape c ≠ .zero := by
  exact shape_mem_flatten_ne_zero (by simpa using hw) hc

def Shape.act : Shape → Vertex → Option Vertex
  | .zero,_ => none
  | .unit,v => some v
  | .path a b,v => if v = a then some b else none

theorem Shape.act_comp : ∀ (a b : Shape) (v : Vertex),
    (a*b).act v = (a.act v).bind b.act := by decide

def walk (v : Vertex) (w : List (Letter C H)) : Option Vertex := (shape w).act v

@[simp] theorem walk_nil (v : Vertex) : walk v ([] : List (Letter C H)) = some v := rfl

theorem walk_cons (v : Vertex) (a : Letter C H) (w : List (Letter C H)) :
    walk v (a::w) = ((typeOf a).act v).bind (fun z => walk z w) := by
  exact Shape.act_comp _ _ _

theorem exists_walk {w : List (Letter C H)} (h : shape w ≠ .zero) :
    ∃ v z, walk v w = some z := by
  cases he : shape w with
  | zero => exact (h he).elim
  | unit => exact ⟨.outer,.outer,by simp [walk,he,Shape.act]⟩
  | path a b => exact ⟨a,b,by simp [walk,he,Shape.act]⟩

/-- A sector cannot have any omega except its last letter. -/
def terminalLeave : List (Letter C H) → Prop
  | [] => True
  | .leave::w => w = []
  | _::w => terminalLeave w

theorem terminalLeave_cons {a : Letter C H} (ha : a ≠ .leave) (w : List (Letter C H)) :
    terminalLeave (a::w) ↔ terminalLeave w := by cases a <;> simp_all [terminalLeave]

theorem terminalLeave_glue (a : Letter C H) (ha : a ≠ .leave)
    (cs : List (List (Letter C H))) (h : ∀ c ∈ cs, terminalLeave c) :
    ∀ c ∈ glue [a] cs, terminalLeave c := by
  cases cs with
  | nil => simp [glue,terminalLeave_cons ha,terminalLeave]
  | cons c cs =>
    simp only [glue,List.cons_append,List.nil_append,List.mem_cons]
    intro d hd
    rcases hd with rfl | hd
    · exact (terminalLeave_cons ha c).2 (h c (by simp))
    · exact h d (List.mem_cons_of_mem _ hd)

theorem terminalLeave_cuts (w : List (Letter C H)) : ∀ c ∈ cuts w, terminalLeave c := by
  induction w with
  | nil => simp
  | cons a w ih =>
    by_cases ha : a = .leave
    · subst a
      simp only [cuts_leave,List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · rfl
      · exact ih c hc
    · rw [cuts_cons ha]
      exact terminalLeave_glue _ ha _ ih

/-- Once a path is at R, its terminal sector consists only of right loops and
    an optional omega. This includes a headless right end-sector. -/
theorem right_form {w : List (Letter C H)} (hn : terminalLeave w) {v : Vertex}
    (h : walk .right w = some v) :
    ∃ r : List C, ∃ rb : Bool, w = r.map .right ++ (if rb then [.leave] else []) := by
  induction w with
  | nil => exact ⟨[],false,rfl⟩
  | cons a w ih =>
    cases a with
    | zero => simp [walk_cons,typeOf,Shape.act] at h
    | enter => simp [walk_cons,typeOf,Shape.act] at h
    | head q => simp [walk_cons,typeOf,Shape.act] at h
    | left c => simp [walk_cons,typeOf,Shape.act] at h
    | leave =>
      have hw : w = [] := hn
      exact ⟨[],true,by simp [hw]⟩
    | right c =>
      have hw : walk .right w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      obtain ⟨r,rb,he⟩ := ih hn hw
      exact ⟨c::r,rb,by simp [he]⟩

/-- Starting at L, a sector either has no head and only left loops, or has
    exactly one head followed by a right-only tail. -/
theorem left_form {w : List (Letter C H)} (hn : terminalLeave w) {v : Vertex}
    (h : walk .left w = some v) :
    (∃ l : List C, w = l.map .left) ∨
    (∃ l : List C, ∃ q : H, ∃ r : List C, ∃ rb : Bool,
      w = l.map .left ++ [.head q] ++ r.map .right ++ (if rb then [.leave] else [])) := by
  induction w with
  | nil => exact .inl ⟨[],rfl⟩
  | cons a w ih =>
    cases a with
    | zero => simp [walk_cons,typeOf,Shape.act] at h
    | enter => simp [walk_cons,typeOf,Shape.act] at h
    | leave => simp [walk_cons,typeOf,Shape.act] at h
    | right c => simp [walk_cons,typeOf,Shape.act] at h
    | head q =>
      have hw : walk .right w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      obtain ⟨r,rb,he⟩ := right_form (w := w) hn hw
      exact .inr ⟨[],q,r,rb,by simp [he]⟩
    | left c =>
      have hw : walk .left w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      rcases ih hn hw with ⟨l,he⟩ | ⟨l,q,r,rb,he⟩
      · exact .inl ⟨c::l,by simp [he]⟩
      · exact .inr ⟨c::l,q,r,rb,by simp [he]⟩

/-- Every nonzero sector is either literally headless or has the precise
    optional-boundary zipper grammar used by the finite component evaluator. -/
theorem sector_form {w : List (Letter C H)} (hn : terminalLeave w)
    (h : shape w ≠ .zero) : heads w = [] ∨
    ∃ l q r lb rb, w = headed l q r lb rb := by
  obtain ⟨v,z,hv⟩ := exists_walk h
  cases v with
  | right =>
    obtain ⟨r,rb,rfl⟩ := right_form hn hv
    left
    cases rb <;> simp [heads,List.filterMap_map]
  | left =>
    rcases left_form hn hv with ⟨l,rfl⟩ | ⟨l,q,r,rb,rfl⟩
    · left; simp [heads,List.filterMap_map]
    · right; exact ⟨l.reverse,q,r,false,rb,by simp [headed]⟩
  | outer =>
    cases w with
    | nil => exact .inl rfl
    | cons a w =>
      cases a with
      | zero => simp [walk_cons,typeOf,Shape.act] at hv
      | leave => simp [walk_cons,typeOf,Shape.act] at hv
      | head q => simp [walk_cons,typeOf,Shape.act] at hv
      | left c => simp [walk_cons,typeOf,Shape.act] at hv
      | right c => simp [walk_cons,typeOf,Shape.act] at hv
      | enter =>
        have hw : walk .left w = some z := by simpa [walk_cons,typeOf,Shape.act] using hv
        rcases left_form (w := w) hn hw with ⟨l,rfl⟩ | ⟨l,q,r,rb,rfl⟩
        · left; simp [heads,List.filterMap_map]
        · right; exact ⟨l.reverse,q,r,true,rb,by simp [headed]⟩

theorem cut_form {w : List (Letter C H)} (h : shape w ≠ .zero)
    {c : List (Letter C H)} (hc : c ∈ cuts w) : heads c = [] ∨
      ∃ l q r lb rb, c = headed l q r lb rb :=
  sector_form (terminalLeave_cuts _ _ hc) (shape_cut_ne_zero h hc)

structure Sector (C H : Type*) where
  left : List C
  head : H
  right : List C
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

def encode (v : Sector C H) : List (Letter C H) :=
  headed v.left v.head v.right v.leftBoundary v.rightBoundary

theorem encode_injective : Function.Injective (encode : Sector C H → List (Letter C H)) := by
  intro v w he
  cases v with | mk l q r lb rb =>
  cases w with | mk l' q' r' lb' rb' =>
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := headed_injective he
  rfl

@[simp] theorem enter_mem_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (Letter.enter : Letter C H) ∈ headed l q r lb rb ↔ lb = true := by
  cases lb <;> cases rb <;> simp [headed]

@[simp] theorem leave_mem_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (Letter.leave : Letter C H) ∈ headed l q r lb rb ↔ rb = true := by
  cases lb <;> cases rb <;> simp [headed]

variable [DecidableEq C] [DecidableEq H]

/-- An entirely literal decoder, including a final equality check. It does not
    assume that its input is a path or that any tag is clean. -/
def decode (w : List (Letter C H)) : Option (Sector C H) :=
  match heads w with
  | [q] =>
    let v : Sector C H := ⟨(lefts w).reverse,q,rights w,
      decide (.enter ∈ w),decide (.leave ∈ w)⟩
    if encode v = w then some v else none
  | _ => none

@[simp] theorem decode_encode (v : Sector C H) : decode (encode v) = some v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  simp only [encode,decode,heads_headed,lefts_headed,rights_headed,List.reverse_reverse,
    enter_mem_headed,leave_mem_headed,Bool.decide_eq_true]
  rfl

theorem decode_sound {w : List (Letter C H)} {v : Sector C H} (h : decode w = some v) :
    encode v = w := by
  unfold decode at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      assumption
    · cases h
  · cases h

theorem decode_none_of_headless {w : List (Letter C H)} (h : heads w = []) :
    decode w = none := by simp [decode,h]

theorem decode_complete {w : List (Letter C H)} (hn : terminalLeave w) (h : shape w ≠ .zero)
    (hh : heads w ≠ []) : ∃ v, decode w = some v := by
  rcases sector_form hn h with he | ⟨l,q,r,lb,rb,rfl⟩
  · exact (hh he).elim
  · exact ⟨⟨l,q,r,lb,rb⟩,decode_encode (⟨l,q,r,lb,rb⟩ : Sector C H)⟩

theorem cut_decode_complete {w : List (Letter C H)} (h : shape w ≠ .zero)
    {c : List (Letter C H)} (hc : c ∈ cuts w) :
    heads c = [] ∨ ∃ v, decode c = some v := by
  by_cases hh : heads c = []
  · exact .inl hh
  · exact .inr (decode_complete (terminalLeave_cuts _ _ hc) (shape_cut_ne_zero h hc) hh)

/-- The shortlex order of literal encodings, fixed independently of a budget.
    The alphabet order may be the concrete compiler's numerical symbol order. -/
abbrev shortlex [LinearOrder (Letter C H)] : LinearOrder (Sector C H) :=
  LinearOrder.lift' (fun v => toLex ((encode v).length,encode v)) (by
    intro v w h
    apply encode_injective
    exact congrArg Prod.snd (toLex.injective h))

end

section
open Relation
variable {C H : Type*}

/-- A single literal equation step in arbitrary word context. -/
inductive Context (r : List (Letter C H) → List (Letter C H) → Prop) :
    List (Letter C H) → List (Letter C H) → Prop
  | apply (x y : List (Letter C H)) {a b} (h : r a b) :
      Context r (x++a++y) (x++b++y)

theorem context_context {r : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context r u v) (x y : List (Letter C H)) :
    Context r (x++u++y) (x++v++y) := by
  cases h with
  | apply a b h =>
    simpa only [List.append_assoc] using (Context.apply (x++a) (b++y) h)

theorem reaches_context {r : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : ReflTransGen (Context r) u v) (x y : List (Letter C H)) :
    ReflTransGen (Context r) (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ hh => context_context hh x y)

/-- These are exactly the absorbing-letter and incompatible-arrow equations,
    oriented toward the zero letter. -/
inductive ZeroStep : List (Letter C H) → List (Letter C H) → Prop
  | pair (a b : Letter C H) (h : typeOf a * typeOf b = .zero) : ZeroStep [a,b] [.zero]

theorem Shape.middle_zero : ∀ (a b c : Shape), b ≠ .unit →
    ((a*b)*c = .zero ↔ a*b = .zero ∨ b*c = .zero) := by decide

theorem absorb_zero (w : List (Letter C H)) :
    ReflTransGen (Context ZeroStep) (.zero::w) [.zero] := by
  induction w with
  | nil => exact .refl
  | cons a w ih =>
    apply ReflTransGen.head ?_ ih
    exact Context.apply [] w (ZeroStep.pair .zero a rfl)

/-- Every dirty nonpath, including every occurrence of Omega, has a finite
    zero derivation. No simulation, program call, or confluence is used. -/
theorem zero_reaches {w : List (Letter C H)} (h : shape w = .zero) :
    ReflTransGen (Context ZeroStep) w [.zero] := by
  induction w with
  | nil => cases h
  | cons a w ih =>
    cases w with
    | nil =>
      cases a <;> simp only [shape_singleton,typeOf] at h
      · exact .refl
      all_goals cases h
    | cons b w =>
      have hz : (typeOf a * typeOf b) * shape w = .zero := by
        simpa only [shape_cons,mul_assoc] using h
      rcases (Shape.middle_zero _ _ _ (typeOf_ne_unit b)).mp hz with hp | ht
      · exact ReflTransGen.head (Context.apply [] w (ZeroStep.pair a b hp)) (absorb_zero w)
      · have hh := reaches_context (ih ht) [a] []
        have hh' : ReflTransGen (Context ZeroStep) (a::b::w) [a,.zero] := by simpa using hh
        exact hh'.tail (Context.apply [] [] (ZeroStep.pair a .zero (mul_zero _)))

/-- Additive grade on literal words. The head and boundary letters each have
    grade one, while all cell-tag data is ignored by a supplied base grade. -/
def letterGrade (g : C → ℕ) : Letter C H → ℕ
  | .zero => 0
  | .left c | .right c => g c
  | _ => 1

def grade (g : C → ℕ) (w : List (Letter C H)) : ℕ := (w.map (letterGrade g)).sum

@[simp] theorem grade_nil (g : C → ℕ) : grade g ([] : List (Letter C H)) = 0 := rfl
@[simp] theorem grade_cons (g : C → ℕ) (a : Letter C H) (w : List (Letter C H)) :
    grade g (a::w) = letterGrade g a + grade g w := rfl
@[simp] theorem grade_append (g : C → ℕ) (u v : List (Letter C H)) :
    grade g (u++v) = grade g u + grade g v := by simp [grade]

theorem context_grade {r : List (Letter C H) → List (Letter C H) → Prop} (g : C → ℕ)
    (hr : ∀ u v, r u v → grade g v ≤ grade g u) {u v : List (Letter C H)}
    (h : Context r u v) : grade g v ≤ grade g u := by
  cases h with
  | apply x y h =>
    simp only [grade_append]
    exact Nat.add_le_add_right (Nat.add_le_add_left (hr _ _ h) _) _

theorem zeroStep_grade (g : C → ℕ) {u v : List (Letter C H)} (h : ZeroStep u v) :
    grade g v ≤ grade g u := by cases h; simp [grade,letterGrade]

theorem zero_context_grade (g : C → ℕ) {u v : List (Letter C H)} (h : Context ZeroStep u v) :
    grade g v ≤ grade g u := context_grade g (fun _ _ => zeroStep_grade g) h

@[simp] theorem grade_headed (g : C → ℕ) (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    grade g (headed l q r lb rb) = (l.map g).sum + 1 + (r.map g).sum +
      (if lb then 1 else 0) + (if rb then 1 else 0) := by
  cases lb <;> cases rb <;> simp [headed,grade,letterGrade,List.map_reverse,List.map_map,Function.comp_def] <;> ac_rfl

end

section
variable {C H : Type*}

 theorem glue_append_of_ne_nil (u : List (Letter C H))
    (cs ds : List (List (Letter C H))) (h : cs ≠ []) :
    glue u (cs++ds) = glue u cs ++ ds := by
  cases cs with
  | nil => exact (h rfl).elim
  | cons c cs => rfl

 theorem cuts_append_leave (u v : List (Letter C H)) :
    cuts (u ++ .leave::v) = cuts (u++[.leave]) ++ cuts v := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    by_cases ha : a = .leave
    · subst a
      simp only [List.cons_append,cuts_leave,ih]
    · simp only [List.cons_append,cuts_cons ha,ih]
      apply glue_append_of_ne_nil
      intro hh
      have := congrArg List.flatten hh
      simp at this

/-- Split an arbitrary left context after its last omega. The finished part
    cannot join the sector containing a subsequently inserted head. -/
theorem split_left_context (x : List (Letter C H)) :
    ∃ p a, x = p++a ∧ (.leave : Letter C H) ∉ a ∧
      (p = [] ∨ ∃ t, p = t++[.leave]) := by
  induction x with
  | nil => exact ⟨[],[],rfl,by simp,.inl rfl⟩
  | cons c x ih =>
    obtain ⟨p,a,rfl,ha,hp⟩ := ih
    rcases hp with rfl | ⟨t,rfl⟩
    · by_cases hc : c = .leave
      · subst c
        exact ⟨[.leave],a,rfl,ha,.inr ⟨[],rfl⟩⟩
      · exact ⟨[],c::a,rfl,by simpa using And.intro (Ne.symm hc) ha,.inl rfl⟩
    · exact ⟨c::(t++[.leave]),a,rfl,ha,.inr ⟨c::t,rfl⟩⟩

/-- One delimiter frame works simultaneously for every nonempty replacement
    with no omega. This lemma makes no path or cleanliness assumption. -/
theorem context_frame (x y : List (Letter C H)) :
    ∃ cs a b ds, (.leave : Letter C H) ∉ a ∧ terminalLeave b ∧
      (∀ u : List (Letter C H), u ≠ [] → .leave ∉ u →
        cuts (x++u++y) = cs ++ (a++u++b)::ds) := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  cases hy : cuts y with
  | nil =>
    have hy' : y = [] := by simpa using congrArg List.flatten hy
    subst y
    refine ⟨cuts p,a,[],[],ha,trivial,?_⟩
    intro u hu hn
    simp only [List.append_nil,List.append_assoc]
    rw [hclosed,cuts_append_nonleave a _ ha,cuts_of_noLeave u hn]
    cases u with
    | nil => exact (hu rfl).elim
    | cons c u => simp [glue]
  | cons b ds =>
    have hb : terminalLeave b := terminalLeave_cuts y b (by simp [hy])
    refine ⟨cuts p,a,b,ds,ha,hb,?_⟩
    intro u _ hn
    simp only [List.append_assoc]
    rw [hclosed,cuts_append_nonleave a _ ha,
      cuts_append_nonleave u y hn,hy,glue_assoc]
    simp only [glue,List.append_assoc]

 theorem terminalLeave_append_nonleave (a b : List (Letter C H))
    (ha : .leave ∉ a) (hb : terminalLeave b) : terminalLeave (a++b) := by
  induction a with
  | nil => exact hb
  | cons c a ih =>
    have hc : c ≠ .leave := fun h => ha (by simp [h])
    exact (terminalLeave_cons hc _).2 (ih (fun h => ha (List.mem_cons_of_mem _ h)))

/-- The unique designated head identifies its entire host sector, even when
    the surrounding input is malformed. The only premise is literal pathhood. -/
theorem head_context_form {a b : List (Letter C H)} {q : H}
    (hn : terminalLeave (a++ .head q::b)) (h : shape (a++ .head q::b) ≠ .zero) :
    ∃ (l r : List C) (lb rb : Bool), a = (if lb then [.enter] else []) ++ l.reverse.map .left ∧
      b = r.map .right ++ (if rb then [.leave] else []) := by
  rcases sector_form hn h with hh | ⟨l,z,r,lb,rb,he⟩
  · simp only [heads,List.filterMap_append,List.filterMap_cons] at hh
    simp at hh
  · have hp : (.head q : Letter C H) ∉
        (if lb then [Letter.enter] else []) ++ l.reverse.map .left := by
      cases lb <;> simp
    have hs : (.head q : Letter C H) ∉
        r.map .right ++ (if rb then [Letter.leave] else []) := by
      cases rb <;> simp
    have he' : (if lb then [Letter.enter] else []) ++ l.reverse.map .left ++
        .head z::(r.map .right ++ (if rb then [Letter.leave] else [])) = a++ .head q::b := by
      simpa only [headed,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using he.symm
    obtain ⟨ha,_,hb⟩ := (List.append_cons_inj_of_notMem hp hs).mp he'
    exact ⟨l,r,lb,rb,ha.symm,hb.symm⟩

/-- Extract the containing sector in an arbitrary path context. The same
    surrounding sector list works after any head change, or any added left and
    right loops. No claim that sector boundaries survive arbitrary attachment
    of context is built into the statement. -/
theorem head_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q]++y) ≠ .zero) :
    ∃ cs ds l r lb rb, ∀ (q' : H) (ls rs : List C),
      cuts (x++ls.map .left++[.head q']++rs.map .right++y) =
        cs ++ [headed (ls.reverse++l) q' (rs++r) lb rb] ++ ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := context_frame x y
  have hf := hframe [.head q] (by simp) (by simp)
  have hm : shape (a++ .head q::b) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl (by simp))
  have ht : terminalLeave (a++ .head q::b) :=
    terminalLeave_append_nonleave a _ ha ((terminalLeave_cons (by simp) b).2 hb)
  obtain ⟨l,r,lb,rb,rfl,rfl⟩ := head_context_form ht hm
  refine ⟨cs,ds,l,r,lb,rb,?_⟩
  intro q' ls rs
  have hh := hframe (ls.map .left++[.head q']++rs.map .right) (by simp) (by simp)
  simpa only [headed,List.reverse_append,List.reverse_reverse,List.map_append,
    List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hh

 theorem split_right_context (y : List (Letter C H)) :
    ∃ b s, y = b++s ∧ terminalLeave b ∧
      (s = [] ∨ ∃ t, b = t++[.leave]) := by
  induction y with
  | nil => exact ⟨[],[],rfl,trivial,.inl rfl⟩
  | cons c y ih =>
    by_cases hc : c = .leave
    · subst c
      exact ⟨[.leave],y,rfl,rfl,.inr ⟨[],rfl⟩⟩
    · obtain ⟨b,s,rfl,hb,hs⟩ := ih
      refine ⟨c::b,s,rfl,(terminalLeave_cons hc b).2 hb,?_⟩
      rcases hs with rfl | ⟨t,rfl⟩
      · exact .inl rfl
      · exact .inr ⟨c::t,rfl⟩

/-- A two-sided delimiter frame, valid even for replacements which change the
    number of heads or create/delete internal visits to the outer vertex. -/
theorem general_context_frame (x y : List (Letter C H)) :
    ∃ cs a b ds, (.leave : Letter C H) ∉ a ∧ terminalLeave b ∧
      (∀ u, cuts (x++u++y) = cs ++ cuts (a++u++b) ++ ds) := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  obtain ⟨b,s,rfl,hb,hs⟩ := split_right_context y
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  have hright : ∀ v, cuts (v++b++s) = cuts (v++b) ++ cuts s := by
    intro v
    rcases hs with rfl | ⟨t,rfl⟩
    · simp
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave (v++t) s
  refine ⟨cuts p,a,b,cuts s,ha,hb,?_⟩
  intro u
  rw [show (p++a)++u++(b++s) = p++((a++u)++b++s) by simp [List.append_assoc],
    hclosed,hright]
  simp only [List.append_assoc]

/-- Around a fixed head every path context is exactly an arbitrary prefix of
    finished sectors, an optional alpha and left loops, right loops and an
    optional omega, and an arbitrary suffix of sectors. This uniform literal
    identity is also valid for merge and unmerge replacements. -/
theorem word_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (l r : List C) (lb rb : Bool), ∀ u,
      cuts (x++u++y) = cs ++
        cuts (((if lb then [.enter] else []) ++ l.reverse.map .left) ++ u ++
          (r.map .right ++ (if rb then [.leave] else []))) ++ ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := general_context_frame x y
  have hf := congrArg List.flatten (hframe [.head q])
  simp only [List.flatten_append,flatten_cuts] at hf
  have hm : shape (a++ .head q::b) ≠ .zero := by
    rw [hf] at h
    have hh := (shape_append_ne_zero h).1
    have hh' := (shape_append_ne_zero hh).2
    simpa using hh'
  have ht : terminalLeave (a++ .head q::b) :=
    terminalLeave_append_nonleave a _ ha ((terminalLeave_cons (by simp) b).2 hb)
  obtain ⟨l,r,lb,rb,rfl,rfl⟩ := head_context_form ht hm
  exact ⟨cs,ds,l,r,lb,rb,hframe⟩

end

section
variable {C H : Type*} [DecidableEq C] [DecidableEq H]

/-- Preprocessing is applied only to headed sectors. Headless pieces retain
    their literal words; no implicit boundary or identity generator is added. -/
def prepareChunk (P : Sector C H → List (Sector C H)) (w : List (Letter C H)) :
    List (List (Letter C H)) :=
  match decode w with
  | none => [w]
  | some v => (P v).map encode

def prepareChunks (P : Sector C H → List (Sector C H))
    (cs : List (List (Letter C H))) : List (List (Letter C H)) := cs.flatMap (prepareChunk P)

def prepare (P : Sector C H → List (Sector C H)) (w : List (Letter C H)) :
    List (List (Letter C H)) := prepareChunks P (cuts w)

@[simp] theorem prepareChunk_encode (P : Sector C H → List (Sector C H)) (v : Sector C H) :
    prepareChunk P (encode v) = (P v).map encode := by simp [prepareChunk]

@[simp] theorem prepareChunks_append (P : Sector C H → List (Sector C H))
    (cs ds : List (List (Letter C H))) :
    prepareChunks P (cs++ds) = prepareChunks P cs ++ prepareChunks P ds := by
  simp [prepareChunks]

 theorem prepareChunks_singleton (P : Sector C H → List (Sector C H)) (v : Sector C H) :
    prepareChunks P [encode v] = (P v).map encode := by simp [prepareChunks]

/-- All ordinary compiler rules can be checked on a sector with arbitrary
    extra zipper cells. This theorem transports those checks into arbitrary
    literal word contexts, without a cleanliness or boundary promise. -/
theorem prepare_context_headed (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (l₁ l₂ r₁ r₂ : List C) (q₁ q₂ : H)
    (h : shape (x++headed l₁ q₁ r₁ false false++y) ≠ .zero)
    (hinv : ∀ (l r : List C) (lb rb : Bool),
      P ⟨l₁++l,q₁,r₁++r,lb,rb⟩ = P ⟨l₂++l,q₂,r₂++r,lb,rb⟩) :
    prepare P (x++headed l₁ q₁ r₁ false false++y) =
      prepare P (x++headed l₂ q₂ r₂ false false++y) := by
  have hb : shape (x++[.head q₁]++y) ≠ .zero := by
    simpa only [shape_append,shape_headed,shape_singleton,typeOf,Bool.false_eq_true,ite_false] using h
  obtain ⟨cs,ds,l,r,lb,rb,hframe⟩ := head_frame x y q₁ hb
  have hf₁ := hframe q₁ l₁.reverse r₁
  have hf₂ := hframe q₂ l₂.reverse r₂
  simp only [List.reverse_reverse] at hf₁ hf₂
  have h₁ : cuts (x++headed l₁ q₁ r₁ false false++y) =
      cs++[encode (⟨l₁++l,q₁,r₁++r,lb,rb⟩ : Sector C H)]++ds := by
    simpa only [headed,encode,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
      List.append_assoc] using hf₁
  have h₂ : cuts (x++headed l₂ q₂ r₂ false false++y) =
      cs++[encode (⟨l₂++l,q₂,r₂++r,lb,rb⟩ : Sector C H)]++ds := by
    simpa only [headed,encode,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
      List.append_assoc] using hf₂
  simp only [prepare,h₁,h₂,prepareChunks_append,prepareChunks_singleton,hinv]

end

section
variable {C H : Type*}

 theorem prefix_end_enter {a : List (Letter C H)} {l : List C} {lb : Bool}
    (h : a++[.enter] = (if lb then [.enter] else []) ++ l.reverse.map .left) :
    a = [] ∧ l = [] ∧ lb = true := by
  cases l with
  | nil =>
    cases lb with
    | false => simp at h
    | true =>
      refine ⟨?_,rfl,rfl⟩
      apply List.append_left_injective [.enter]
      simpa using h
  | cons c l =>
    have hh := congrArg (fun w : List (Letter C H) => w.reverse.head?) h
    cases lb <;> simp [List.reverse_cons,List.reverse_append] at hh

 theorem suffix_begin_leave {b : List (Letter C H)} {r : List C} {rb : Bool}
    (h : .leave::b = r.map .right ++ (if rb then [.leave] else [])) :
    b = [] ∧ r = [] ∧ rb = true := by
  cases r with
  | nil => cases rb <;> simp_all
  | cons c r => simp at h

 theorem left_boundary_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.enter,.head q]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (r : List C) (rb : Bool), ∀ q' : H,
      cuts (x++[.enter,.head q']++y) = cs++[headed [] q' r true rb]++ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := context_frame x y
  have hf := hframe [.enter,.head q] (by simp) (by simp)
  have hm : shape ((a++[.enter])++ .head q::b) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl (by simp))
  have ht : terminalLeave ((a++[.enter])++ .head q::b) := by
    apply terminalLeave_append_nonleave
    · simpa using ha
    · exact (terminalLeave_cons (by simp) b).2 hb
  obtain ⟨l,r,lb,rb,hl,hr⟩ := head_context_form ht hm
  obtain ⟨rfl,rfl,rfl⟩ := prefix_end_enter hl
  subst b
  refine ⟨cs,ds,r,rb,?_⟩
  intro q'
  simpa [headed,List.append_assoc] using hframe [.enter,.head q'] (by simp) (by simp)

 theorem right_boundary_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q,.leave]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (l : List C) (lb : Bool), ∀ q' : H,
      cuts (x++[.head q',.leave]++y) = cs++[headed l q' [] lb true]++ds := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  have hf : ∀ q' : H, cuts ((p++a)++[.head q',.leave]++y) =
      cuts p ++ (a++[.head q',.leave])::cuts y := by
    intro q'
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hclosed,cuts_append_nonleave a _ ha,cuts_cons (by simp),cuts_leave]
    simp [glue]
  have hm : shape (a++ .head q::[.leave]) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl trivial)
  have ht : terminalLeave (a++ .head q::[.leave]) :=
    terminalLeave_append_nonleave a _ ha (by trivial)
  obtain ⟨l,r,lb,rb,hl,hr⟩ := head_context_form ht hm
  obtain ⟨_,rfl,rfl⟩ := suffix_begin_leave hr
  subst a
  refine ⟨cuts p,cuts y,l,lb,?_⟩
  intro q'
  simpa [headed,List.append_assoc] using hf q'

variable [DecidableEq C] [DecidableEq H]

theorem prepare_context_left_boundary (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q₁ q₂ : H)
    (h : shape (x++[.enter,.head q₁]++y) ≠ .zero)
    (hinv : ∀ (r : List C) (rb : Bool), P ⟨[],q₁,r,true,rb⟩ = P ⟨[],q₂,r,true,rb⟩) :
    prepare P (x++[.enter,.head q₁]++y) = prepare P (x++[.enter,.head q₂]++y) := by
  obtain ⟨cs,ds,r,rb,hframe⟩ := left_boundary_frame x y q₁ h
  simp only [prepare,hframe,prepareChunks_append]
  change prepareChunks P cs ++ prepareChunks P [encode ⟨[],q₁,r,true,rb⟩] ++ prepareChunks P ds =
    prepareChunks P cs ++ prepareChunks P [encode ⟨[],q₂,r,true,rb⟩] ++ prepareChunks P ds
  rw [prepareChunks_singleton,prepareChunks_singleton,hinv]

theorem prepare_context_right_boundary (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q₁ q₂ : H)
    (h : shape (x++[.head q₁,.leave]++y) ≠ .zero)
    (hinv : ∀ (l : List C) (lb : Bool), P ⟨l,q₁,[],lb,true⟩ = P ⟨l,q₂,[],lb,true⟩) :
    prepare P (x++[.head q₁,.leave]++y) = prepare P (x++[.head q₂,.leave]++y) := by
  obtain ⟨cs,ds,l,lb,hframe⟩ := right_boundary_frame x y q₁ h
  simp only [prepare,hframe,prepareChunks_append]
  change prepareChunks P cs ++ prepareChunks P [encode ⟨l,q₁,[],lb,true⟩] ++ prepareChunks P ds =
    prepareChunks P cs ++ prepareChunks P [encode ⟨l,q₂,[],lb,true⟩] ++ prepareChunks P ds
  rw [prepareChunks_singleton,prepareChunks_singleton,hinv]

end

variable {C H : Type*}

 theorem cuts_join_headed (l r : List C) (q q' : H) (lb rb : Bool) :
    cuts (headed l q [] lb true ++ headed [] q' r true rb) =
      [headed l q [] lb true,headed [] q' r true rb] := by
  let a := (if lb then [Letter.enter] else []) ++ l.reverse.map .left ++ [Letter.head q]
  have ha : headed l q [] lb true = a++[.leave] := by simp [a,headed]
  rw [ha,List.append_assoc,List.singleton_append,cuts_append_leave,←ha,cuts_headed,cuts_headed]
  rfl

variable [DecidableEq C] [DecidableEq H]

/-- Literal merge invariance in every well-typed context, including incomplete
    and dirty outer sectors. The two visits to the outer vertex are explicit. -/
theorem prepare_context_merge (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q p : H) (c d : C)
    (h : shape (x++[.head q,.leave,.enter,.head q]++y) ≠ .zero)
    (hinv : ∀ (l r : List C) (lb rb : Bool),
      P ⟨c::l,p,d::r,lb,rb⟩ = P ⟨l,q,[],lb,true⟩ ++ P ⟨[],q,r,true,rb⟩) :
    prepare P (x++[.head q,.leave,.enter,.head q]++y) =
      prepare P (x++[.left c,.head p,.right d]++y) := by
  have hb : shape (x++[.head q]++y) ≠ .zero := by
    simpa only [shape_append,shape_cons,shape_nil,typeOf,mul_unit,path_mul_path,
      ite_true] using h
  obtain ⟨cs,ds,l,r,lb,rb,hframe⟩ := word_frame x y q hb
  have hf₁ : cuts (x++[.head q,.leave,.enter,.head q]++y) =
      cs++[encode ⟨l,q,[],lb,true⟩,encode ⟨[],q,r,true,rb⟩]++ds := by
    rw [hframe]
    have he : ((if lb then [Letter.enter] else [])++l.reverse.map .left) ++
        [.head q,.leave,.enter,.head q] ++ (r.map .right++(if rb then [.leave] else [])) =
        headed l q [] lb true ++ headed [] q r true rb := by
      simp [headed,List.append_assoc]
    rw [he,cuts_join_headed]
    rfl
  have hf₂ : cuts (x++[.left c,.head p,.right d]++y) =
      cs++[encode ⟨c::l,p,d::r,lb,rb⟩]++ds := by
    rw [hframe]
    have he : ((if lb then [Letter.enter] else [])++l.reverse.map .left) ++
        [.left c,.head p,.right d] ++ (r.map .right++(if rb then [.leave] else [])) =
        headed (c::l) p (d::r) lb rb := by
      simp [headed,List.reverse_cons,List.map_append,List.append_assoc]
    rw [he,cuts_headed]
    rfl
  unfold prepare
  rw [hf₁,hf₂]
  simp only [prepareChunks,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,prepareChunk_encode,List.append_nil,hinv,List.map_append,
    List.append_assoc]

end FiniteAlgebraicEnvelopes.Compiler.Path

/- Maximal full-raw-run normalization and its one exceptional equation,
   the finite compiler. Nonraw sectors are opaque separators here. -/

end OAI
