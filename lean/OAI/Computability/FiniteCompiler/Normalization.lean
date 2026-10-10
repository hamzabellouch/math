import OAI.Computability.FiniteCompiler.Paths

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

abbrev Item (C S : Type*) := Sum C (List S)

/-- Full raw sectors have three structural letters alpha,Q,omega. -/
def itemGrade (g : C → ℕ) : Item C S → ℕ
  | .inl c => g c
  | .inr w => w.length + 3

def grade (g : C → ℕ) (w : List (Item C S)) : ℕ := (w.map (itemGrade g)).sum

@[simp] theorem grade_nil (g : C → ℕ) : grade g ([] : List (Item C S)) = 0 := rfl
@[simp] theorem grade_cons (g : C → ℕ) (a : Item C S) (w : List (Item C S)) :
    grade g (a::w) = itemGrade g a + grade g w := rfl
@[simp] theorem grade_append (g : C → ℕ) (u v : List (Item C S)) :
    grade g (u++v) = grade g u + grade g v := by simp [grade]

/-- Fold a nonempty raw run by adjacent pair replacement. We prove below that
    it agrees with the source's single call on the concatenated maximal run. -/
def prepend (f : List S → List S) : Item C S → List (Item C S) → List (Item C S)
  | .inr x,.inr y::w => .inr (f (x++y))::w
  | a,w => a::w

def normalize (f : List S → List S) : List (Item C S) → List (Item C S)
  | [] => []
  | a::w => prepend f a (normalize f w)

@[simp] theorem normalize_nil (f : List S → List S) : normalize f ([] : List (Item C S)) = [] := rfl
@[simp] theorem normalize_cons (f : List S → List S) (a : Item C S) (w : List (Item C S)) :
    normalize f (a::w) = prepend f a (normalize f w) := rfl

/-- Budget laws are used only where the *unreduced* concatenation has bounded
    length. They are exactly the totality/length/context interface of the source. -/
structure Budget (f : List S → List S) (m : ℕ) : Prop where
  length : ∀ w, w.length ≤ m → (f w).length ≤ w.length
  context : ∀ x w y, (x++w++y).length ≤ m → f (x++f w++y) = f (x++w++y)

variable {f : List S → List S} {m : ℕ}

 theorem prepend_grade (g : C → ℕ) (h : Budget f m) (a : Item C S) (w : List (Item C S))
    (hm : itemGrade g a + grade g w ≤ m) :
    grade g (prepend f a w) ≤ itemGrade g a + grade g w := by
  cases a with
  | inl c => rfl
  | inr x =>
    cases w with
    | nil => rfl
    | cons b w =>
      cases b with
      | inl c => rfl
      | inr y =>
        have hb : (x++y).length ≤ m := by simp only [grade_cons,itemGrade,List.length_append] at *; omega
        have hl := h.length (x++y) hb
        simp only [prepend,grade_cons,itemGrade,List.length_append] at *
        omega

theorem normalize_grade (g : C → ℕ) (h : Budget f m) (w : List (Item C S))
    (hm : grade g w ≤ m) : grade g (normalize f w) ≤ grade g w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hw : grade g w ≤ m := by simp only [grade_cons] at hm; omega
    have hi := ih hw
    exact (prepend_grade g h a (normalize f w) (by simp only [grade_cons] at hm; omega)).trans
      (by simpa only [grade_cons] using Nat.add_le_add_left hi (itemGrade g a))

/-- The two bracketings of three adjacent raw inputs agree inside the same
    budget. No idempotence assumption on raw singleton sectors is made. -/
theorem triple (h : Budget f m) (x y z : List S)
    (hm : (x++y++z).length ≤ m) : f (x++f (y++z)) = f (f (x++y)++z) := by
  have h₁ := h.context x (y++z) [] (by simpa [List.append_assoc] using hm)
  have h₂ := h.context [] (x++y) z (by simpa using hm)
  simp only [List.append_nil,List.nil_append,List.append_assoc] at h₁ h₂ ⊢
  exact h₁.trans h₂.symm

theorem prepend_pair (g : C → ℕ) (h : Budget f m) (x y : List S) (w : List (Item C S))
    (hm : x.length + y.length + grade g w ≤ m) :
    prepend f (.inr x) (prepend f (.inr y) w) = prepend f (.inr (f (x++y))) w := by
  cases w with
  | nil => rfl
  | cons a w =>
    cases a with
    | inl c => rfl
    | inr z =>
      simp only [prepend]
      congr 2
      apply triple h x y z
      simp only [grade_cons,itemGrade,List.length_append] at *
      omega

/-- Left contexts commute with equality of folded normal forms, without any
    stability-of-sector-boundaries claim. -/
theorem normalize_left_context {u v : List (Item C S)} (h : normalize f u = normalize f v)
    (a : List (Item C S)) : normalize f (a++u) = normalize f (a++v) := by
  induction a with
  | nil => exact h
  | cons a w ih => simpa only [List.cons_append,normalize_cons] using congrArg (prepend f a) ih

/-- Contextual invariance of pair versus its genuine returned singleton; this
    is the only nontrivial comparison at q_ok--cleanup with entry priority. -/
theorem pair_context (g : C → ℕ) (h : Budget f m) (x y : List S) (a b : List (Item C S))
    (hm : grade g (a ++ .inr x :: .inr y :: b) ≤ m) :
    normalize f (a ++ .inr x :: .inr y :: b) =
      normalize f (a ++ .inr (f (x++y)) :: b) := by
  apply normalize_left_context
  simp only [normalize_cons]
  apply prepend_pair g h
  have hb : grade g b ≤ m := by simp only [grade_append,grade_cons,itemGrade] at hm; omega
  have hi := normalize_grade g h b hb
  simp only [grade_append,grade_cons,itemGrade] at hm
  omega

/-- On one full raw sector the evaluator never calls the program. -/
@[simp] theorem normalize_singleton (x : List S) :
    normalize f ([.inr x] : List (Item C S)) = [.inr x] := rfl

/-- On a raw run of size at least two this fold is exactly a single application
    to the literal concatenation, as specified by the frozen source. -/
theorem normalize_run (h : Budget f m) (x y : List S) (ws : List (List S))
    (hm : (x++y++ws.flatten).length ≤ m) :
    normalize f (((x::y::ws).map Sum.inr) : List (Item C S)) =
      [.inr (f (x++y++ws.flatten))] := by
  induction ws generalizing x y with
  | nil => simp [prepend]
  | cons z ws ih =>
    have hb : (y++z++ws.flatten).length ≤ m := by
      simp only [List.flatten_cons,List.length_append] at hm ⊢
      omega
    rw [List.map_cons,normalize_cons,ih y z hb]
    simp only [prepend]
    congr 2
    simpa [List.append_assoc] using h.context x (y++z++ws.flatten) []
      (by simpa [List.append_assoc] using hm)

/-- Split off the entire initial raw run, without changing raw contents. -/
def splitRun : List (Item C S) → List (List S) × List (Item C S)
  | [] => ([],[])
  | .inl c::w => ([],.inl c::w)
  | .inr x::w => let p := splitRun w; (x::p.1,p.2)

@[simp] theorem splitRun_join (w : List (Item C S)) :
    (splitRun w).1.map .inr ++ (splitRun w).2 = w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp_all [splitRun]

theorem splitRun_length (w : List (Item C S)) : (splitRun w).2.length ≤ w.length := by
  have hh := congrArg List.length (splitRun_join w)
  simp only [List.length_append,List.length_map] at hh
  omega

theorem splitRun_stops (w : List (Item C S)) :
    (splitRun w).2 = [] ∨ ∃ c t, (splitRun w).2 = .inl c::t := by
  induction w with
  | nil => exact .inl rfl
  | cons a w ih =>
    cases a with
    | inl c => exact .inr ⟨c,w,rfl⟩
    | inr x => exact ih

@[simp] theorem grade_raws (g : C → ℕ) (ws : List (List S)) :
    grade g (ws.map (Sum.inr : List S → Item C S)) = ws.flatten.length + 3*ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp only [List.map_cons,grade_cons,itemGrade,ih,List.flatten_cons,
      List.length_append,List.length_cons]; omega

theorem prepend_append_separator (a : Item C S) (u v : List (Item C S)) (c : C) :
    prepend f a (u ++ .inl c::v) = prepend f a u ++ .inl c::v := by
  cases a <;> cases u with
  | nil => rfl
  | cons b w => cases b <;> rfl

theorem normalize_append_separator (u v : List (Item C S)) (c : C) :
    normalize f (u ++ .inl c::v) = normalize f u ++ .inl c::normalize f v := by
  induction u with
  | nil => rfl
  | cons a w ih =>
    simp only [List.cons_append,normalize_cons,ih,prepend_append_separator]

/-- The literal source algorithm: a singleton does not invoke f; every longer
    maximal raw run invokes f once on its unmodified concatenation. -/
def source (f : List S → List S) : List (Item C S) → List (Item C S)
  | [] => []
  | .inl c::w => .inl c::source f w
  | .inr x::w =>
    let p := splitRun w
    let z := match p.1 with
      | [] => x
      | _::_ => f (x++p.1.flatten)
    .inr z :: source f p.2
termination_by w => w.length
decreasing_by
  · simp_wf
  · have := splitRun_length w
    simp_wf
    omega

/-- Bounded comparison with the fold is a theorem, not an alteration of the
    source algorithm. In particular source calls obey the same grade budget. -/
theorem source_eq_normalize (g : C → ℕ) (h : Budget f m) (w : List (Item C S))
    (hm : grade g w ≤ m) : source f w = normalize f w := by
  cases w with
  | nil => simp [source]
  | cons a w =>
    cases a with
    | inl c =>
      have hb : grade g w ≤ m := by simp only [grade_cons] at hm; omega
      simp only [source,normalize_cons,prepend,source_eq_normalize g h w hb]
    | inr x =>
      obtain ⟨ys,t,he⟩ : ∃ ys t, splitRun w = (ys,t) := ⟨_,_,rfl⟩
      have hj : ys.map (Sum.inr : List S → Item C S) ++ t = w := by
        simpa only [he] using splitRun_join w
      have ht : t.length ≤ w.length := by simpa only [he] using splitRun_length w
      have hs : t = [] ∨ ∃ c u, t = .inl c::u := by simpa only [he] using splitRun_stops w
      have hb : grade g t ≤ m := by
        rw [← hj] at hm
        simp only [grade_cons,grade_append,itemGrade] at hm
        omega
      have hi := source_eq_normalize g h t hb
      rw [source,he]
      dsimp only
      rw [hi,← hj]
      cases ys with
      | nil =>
        rcases hs with rfl | ⟨c,u,rfl⟩ <;> rfl
      | cons y ys =>
        have hl : (x++y++ys.flatten).length ≤ m := by
          rw [← hj] at hm
          simp only [grade_cons,itemGrade,grade_append,grade_raws,List.flatten_cons,
            List.length_cons,List.length_append] at hm ⊢
          omega
        have hr := normalize_run (C := C) h x y ys hl
        rcases hs with rfl | ⟨c,u,rfl⟩
        · simpa only [List.append_nil,normalize_nil,List.map_cons,List.flatten_cons,
            List.append_assoc] using hr.symm
        · rw [← List.cons_append,← List.map_cons,normalize_append_separator,hr]
          simp only [List.flatten_cons,List.append_assoc,normalize_cons,prepend,
            List.singleton_append]
termination_by w.length
decreasing_by
  all_goals simp_all only [List.length_cons]
  all_goals omega

 theorem source_grade (g : C → ℕ) (h : Budget f m) (w : List (Item C S))
    (hm : grade g w ≤ m) : grade g (source f w) ≤ grade g w := by
  rw [source_eq_normalize g h w hm]
  exact normalize_grade g h w hm

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H B T K : Type*}

/-- Only a change of representation. The cell order and both literal boundary
    flags are retained exactly. -/
def literal (m : H → K) (v : Sector H B T) : Path.Sector (B×T) K :=
  ⟨v.left,m v.head,v.right,v.leftBoundary,v.rightBoundary⟩

def unliteral (v : Path.Sector (B×T) H) : Sector H B T :=
  ⟨v.left,v.head,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem literal_unliteral (v : Path.Sector (B×T) H) : literal id (unliteral v) = v := by
  cases v; rfl
@[simp] theorem unliteral_literal (v : Sector H B T) : unliteral (literal id v) = v := by
  cases v; rfl

 theorem literal_injective (m : H → K) (hm : Function.Injective m) :
    Function.Injective (literal (B := B) (T := T) m) := by
  rintro ⟨l,q,r,a,b⟩ ⟨l',q',r',a',b'⟩ h
  cases Path.Sector.mk.inj h with
  | intro hl hrest =>
    rcases hrest with ⟨hq,hr,ha,hb⟩
    obtain rfl := hl; obtain rfl := hm hq; obtain rfl := hr; obtain rfl := ha; obtain rfl := hb
    rfl

namespace Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path

/-- Zipper fragments of a literal cell instruction, before and after the
    specified cross/stay move. -/
def inLeft (d : Direction) (c : B×T) : List (B×T) := if d = .left then [c] else []
def inRight (d : Direction) (c : B×T) : List (B×T) := if d = .right then [c] else []
def outLeft (d : Direction) (cross : Bool) (c : B×T) : List (B×T) :=
  if (d = .left ∧ cross = false) ∨ (d = .right ∧ cross = true) then [c] else []
def outRight (d : Direction) (cross : Bool) (c : B×T) : List (B×T) :=
  if (d = .right ∧ cross = false) ∨ (d = .left ∧ cross = true) then [c] else []

inductive Rule (table : Table H B T) (m : H → K) :
    List (Letter (B×T) K) → List (Letter (B×T) K) → Prop
  | cell (q : H) (b : B) (t : T) (i : Instruction H T) (h : table.cell q b t = some i) :
      Rule table m
        (headed (inLeft (table.direction q) (b,t)) (m q) (inRight (table.direction q) (b,t)) false false)
        (headed (outLeft (table.direction q) i.cross (b,i.tag)) (m i.head)
          (outRight (table.direction q) i.cross (b,i.tag)) false false)
  | left (q q' : H) (hd : table.direction q = .left) (h : table.boundary q = some q') :
      Rule table m [.enter,.head (m q)] [.enter,.head (m q')]
  | right (q q' : H) (hd : table.direction q = .right) (h : table.boundary q = some q') :
      Rule table m [.head (m q),.leave] [.head (m q'),.leave]

 theorem cell_step (table : Table H B T) (q : H) (b : B) (t : T)
    (i : Instruction H T) (h : table.cell q b t = some i)
    (l r : List (B×T)) (lb rb : Bool) :
    Step table
      ⟨inLeft (table.direction q) (b,t)++l,q,inRight (table.direction q) (b,t)++r,lb,rb⟩
      ⟨outLeft (table.direction q) i.cross (b,i.tag)++l,i.head,
        outRight (table.direction q) i.cross (b,i.tag)++r,lb,rb⟩ := by
  cases hd : table.direction q <;> cases hc : i.cross <;>
    simp [Step,step,inLeft,inRight,outLeft,outRight,hd,hc,h]

 theorem rule_shape (table : Table H B T) (m : H → K) {u v : List (Letter (B×T) K)}
    (h : Rule table m u v) : shape u = shape v := by
  cases h with
  | cell => simp
  | left => simp [typeOf]
  | right => simp [typeOf]

 theorem rule_length (table : Table H B T) (m : H → K) {u v : List (Letter (B×T) K)}
    (h : Rule table m u v) : u.length = 2 ∧ v.length = 2 := by
  cases h with
  | cell q b t i h =>
    cases hd : table.direction q <;> cases hc : i.cross <;>
      simp [headed,inLeft,inRight,outLeft,outRight]
  | left => simp
  | right => simp

variable [DecidableEq B] [DecidableEq T] [DecidableEq K]

/-- Sector invariance for a deterministic table implies literal invariance for
    every cell and boundary equation in every word context. -/
theorem prepare_rule (table : Table H B T) (m : H → K)
    (P : Path.Sector (B×T) K → List (Path.Sector (B×T) K))
    (hinv : ∀ v w, Step table v w → P (literal m v) = P (literal m w))
    {u v : List (Letter (B×T) K)} (h : Rule table m u v)
    (x y : List (Letter (B×T) K)) (hn : shape (x++u++y) ≠ .zero) :
    prepare P (x++u++y) = prepare P (x++v++y) := by
  cases h with
  | cell q b t i hi =>
    apply prepare_context_headed P x y _ _ _ _ _ _ hn
    intro l r lb rb
    exact hinv _ _ (cell_step table q b t i hi l r lb rb)
  | left q q' hd hi =>
    apply prepare_context_left_boundary P x y _ _ hn
    intro r rb
    exact hinv ⟨[],q,r,true,rb⟩ ⟨[],q',r,true,rb⟩ (by simp [Step,step,hd,hi])
  | right q q' hd hi =>
    apply prepare_context_right_boundary P x y _ _ hn
    intro l lb
    exact hinv ⟨l,q,[],lb,true⟩ ⟨l,q',[],lb,true⟩ (by simp [Step,step,hd,hi])

end Literal
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {S Γ Q : Type*}

abbrev Cell (S Γ : Type*) := Base S × Tag S Γ
abbrev Head (S Q : Type*) := Surface.Head (Control.Head S Q)
abbrev Letter (S Γ Q : Type*) := Path.Letter (Cell S Γ) (Head S Q)
abbrev Sector (S Γ Q : Type*) := Path.Sector (Cell S Γ) (Head S Q)

def encode (v : Surface.Sector S Γ (Control.Head S Q)) : List (Letter S Γ Q) :=
  Path.encode (Scan.literal id v)

/-- The actual source equations, separate from the exceptional accepting exit
    for which only the *complete* raw-run evaluator is invariant. -/
inductive Ordinary (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
    [DecidableEq S] [DecidableEq Γ] : List (Letter S Γ Q) → List (Letter S Γ Q) → Prop
  | raw (a : S) : Ordinary A M
      [.left (Validator.cell A.blank (.anchor a)),.head .raw]
      [.head .raw,.right (Validator.cell A.blank (.anchor a))]
  | merge : Ordinary A M [.head .raw,.leave,.enter,.head .raw]
      [.left (Validator.cell A.blank .cutC),.head .pending,.right (Validator.cell A.blank .cutD)]
  | quota : Ordinary A M
      [.left (Validator.cell A.blank .workspace),.head .pending,.right (Validator.cell A.blank .cutD)]
      [.head .pending,.right (Validator.cell A.blank .cutD)]
  | entry : Ordinary A M [.head .pending,.right (Validator.cell A.blank .cutD)]
      [.head (.internal .initial),.right (Validator.cell A.blank .cutD)]
  | internal {u v} (h : Scan.Literal.Rule (Control.table A M) Surface.Head.internal u v) :
      Ordinary A M u v
  | clean (c : Cell S Γ) : Ordinary A M [.left c,.head .cleanup]
      ([.head .cleanup]++((Cleanup.emit c).toList.map (Cleanup.letter A.blank)).map .right)
  | finish : Ordinary A M [.enter,.head .cleanup] [.enter,.head .raw]

inductive Rule (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
    [DecidableEq S] [DecidableEq Γ] : List (Letter S Γ Q) → List (Letter S Γ Q) → Prop
  | zero {u v} (h : Path.ZeroStep u v) : Rule A M u v
  | ordinary {u v} (h : Ordinary A M u v) : Rule A M u v
  | exit : Rule A M [.head (.internal (.machine .ok)),.leave] [.head .cleanup,.leave]

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

 theorem ordinary_shape {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) : shape u = shape v := by
  cases h with
  | internal h => exact Scan.Literal.rule_shape _ _ h
  | clean c => cases he : Cleanup.emit c <;> simp [Cleanup.letter,typeOf]
  | raw => simp [typeOf]
  | merge => simp [typeOf]
  | quota => simp [typeOf]
  | entry => simp [typeOf]
  | finish => simp [typeOf]

 theorem rule_shape {u v : List (Letter S Γ Q)} (h : Rule A M u v) : shape u = shape v := by
  cases h with
  | ordinary h => exact ordinary_shape A M h
  | zero h => cases h with | pair a b h => simpa [typeOf] using h
  | exit => simp [typeOf]

 theorem ordinary_length {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) :
    u.length ≤ 4 ∧ v.length ≤ 4 := by
  cases h with
  | internal h => obtain ⟨h₁,h₂⟩ := Scan.Literal.rule_length _ _ h; omega
  | clean c => cases he : Cleanup.emit c <;> simp
  | raw => simp
  | merge => simp
  | quota => simp
  | entry => simp
  | finish => simp

 theorem rule_length {u v : List (Letter S Γ Q)} (h : Rule A M u v) :
    u.length ≤ 4 ∧ v.length ≤ 4 := by
  cases h with
  | ordinary h => exact ordinary_length A M h
  | zero h => cases h; simp
  | exit => simp

/-- The source presentation is finite, not a schema depending on arbitrary
    sector contexts. Every defining side has at most four letters. -/
theorem rules_finite [Fintype S] [Fintype Γ] [Fintype Q] :
    {p : List (Letter S Γ Q) × List (Letter S Γ Q) | Rule A M p.1 p.2}.Finite := by
  apply ((List.finite_length_le (Letter S Γ Q) 4).prod
    (List.finite_length_le (Letter S Γ Q) 4)).subset
  rintro ⟨u,v⟩ h
  exact rule_length A M h

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

def sectorPreprocess (v : Sector S Γ Q) : List (Sector S Γ Q) :=
  (Surface.preprocess A M (Scan.unliteral v)).map (Scan.literal id)

def preprocess (w : List (Letter S Γ Q)) : List (List (Letter S Γ Q)) :=
  Path.prepare (sectorPreprocess A M) w

@[simp] theorem sectorPreprocess_literal (v : Surface.Sector S Γ (Control.Head S Q)) :
    sectorPreprocess A M (Scan.literal id v) = (Surface.preprocess A M v).map (Scan.literal id) := by
  simp [sectorPreprocess]

/-- Every ordinary source equation has identical preprocessed sector lists in
    any literal nonzero context. Only the accepting exit needs a program law. -/
theorem preprocess_ordinary {u v : List (Letter S Γ Q)} (h : Ordinary A M u v)
    (x y : List (Letter S Γ Q)) (hn : shape (x++u++y) ≠ .zero) :
    preprocess A M (x++u++y) = preprocess A M (x++v++y) := by
  unfold preprocess
  cases h with
  | raw a =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y
      [Validator.cell A.blank (.anchor a)] [] [] [Validator.cell A.blank (.anchor a)] .raw .raw hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_rawStep A M (.slide a l r lb rb))
  | merge =>
    apply Path.prepare_context_merge (sectorPreprocess A M) x y .raw .pending _ _ hn
    intro l r lb rb
    change (Surface.pendingPreprocess A.blank
      ⟨Validator.cell A.blank .cutC::l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩).map _ = _
    rw [show Validator.cell A.blank .cutC::l =
      List.replicate 0 (Validator.cell A.blank .workspace)++Validator.cell A.blank .cutC::l by rfl,
      Surface.pendingPreprocess_merge]
    rfl
  | quota =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y
      [Validator.cell A.blank .workspace] [] [Validator.cell A.blank .cutD]
      [Validator.cell A.blank .cutD] .pending .pending hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_quotaStep A M (.trim l r lb rb))
  | entry =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y [] []
      [Validator.cell A.blank .cutD] [Validator.cell A.blank .cutD] .pending (.internal .initial) hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id)) (Surface.preprocess_entryStep A M l r lb rb)
  | internal h =>
    apply Scan.Literal.prepare_rule _ _ _ ?_ h x y hn
    intro v w hvw
    exact congrArg (fun z => z.map (Scan.literal id)) (Surface.preprocess_internalStep A M hvw)
  | clean c =>
    have hinv := fun l r lb rb => congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_cleanupStep A M (v := ⟨c::l,.cleanup,r,lb,rb⟩)
        (w := ⟨l,.cleanup,(Cleanup.emit c).toList.map (Cleanup.letter A.blank)++r,lb,rb⟩) rfl)
    have hh := Path.prepare_context_headed (sectorPreprocess A M) x y [c] [] []
      ((Cleanup.emit c).toList.map (Cleanup.letter A.blank)) .cleanup .cleanup
    simpa [Path.headed] using hh (by simpa [Path.headed] using hn) hinv
  | finish =>
    apply Path.prepare_context_left_boundary (sectorPreprocess A M) x y .cleanup .raw hn
    intro r rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_cleanupStep A M (v := ⟨[],.cleanup,r,true,rb⟩)
        (w := ⟨[],.raw,r,true,rb⟩) rfl)

end

section
open Relation
variable {S Γ Q : Type*}

def gradeCell (c : Cell S Γ) : ℕ := Cleanup.grade c.1
def grade (w : List (Letter S Γ Q)) : ℕ := Path.grade gradeCell w
def chunksGrade (ws : List (List (Letter S Γ Q))) : ℕ := (ws.map grade).sum

@[simp] theorem grade_encode (v : Surface.Sector S Γ (Control.Head S Q)) :
    grade (encode v) = Surface.grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  simp [grade,encode,Scan.literal,Path.encode,Path.grade_headed,Surface.grade,
    Cleanup.cellsGrade,Function.comp_def]
  rfl

@[simp] theorem grade_append (u v : List (Letter S Γ Q)) : grade (u++v) = grade u+grade v :=
  Path.grade_append _ _ _

@[simp] theorem chunksGrade_append (u v : List (List (Letter S Γ Q))) :
    chunksGrade (u++v) = chunksGrade u+chunksGrade v := by simp [chunksGrade]

@[simp] theorem chunksGrade_flatten (ws : List (List (Letter S Γ Q))) :
    grade ws.flatten = chunksGrade ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatten_cons,chunksGrade,ih]

@[simp] theorem grade_raw (b : Γ) (w : List S) :
    grade (encode (Surface.raw (H := Control.Head S Q) b w)) = w.length + 3 := by
  rw [grade_encode]
  simp [Surface.raw,Surface.grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade,List.map_map,
    Function.comp_def]
  omega

 theorem grade_letter_le (a : Letter S Γ Q) : Path.letterGrade (gradeCell (S := S) (Γ := Γ)) a ≤ 2 := by
  cases a with
  | left c | right c => rcases c with ⟨b,t⟩; cases b <;> simp [Path.letterGrade,gradeCell,Cleanup.grade]
  | zero => simp [Path.letterGrade]
  | enter | leave | head _ => simp [Path.letterGrade]

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

 theorem sectorPreprocess_grade (v : Sector S Γ Q) :
    chunksGrade ((sectorPreprocess A M v).map Path.encode) ≤ grade (Path.encode v) := by
  have h := Surface.preprocess_grade A M (Scan.unliteral v)
  have he : Path.encode v = encode (Scan.unliteral v) := by simp [encode]
  rw [he,grade_encode]
  simpa only [chunksGrade,sectorPreprocess,List.map_map,Function.comp_def,
    show (fun x : Surface.Sector S Γ (Control.Head S Q) => grade (Path.encode (Scan.literal id x))) =
      Surface.grade from funext grade_encode,Surface.listGrade] using h

 theorem prepareChunk_grade (w : List (Letter S Γ Q)) :
    chunksGrade (Path.prepareChunk (sectorPreprocess A M) w) ≤ grade w := by
  cases he : Path.decode w with
  | none => simp [Path.prepareChunk,he,chunksGrade]
  | some v =>
    have hw := Path.decode_sound he
    rw [←hw]
    simpa using sectorPreprocess_grade A M v

 theorem prepareChunks_grade (ws : List (List (Letter S Γ Q))) :
    chunksGrade (Path.prepareChunks (sectorPreprocess A M) ws) ≤ chunksGrade ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simpa only [Path.prepareChunks,List.flatMap_cons,chunksGrade_append,
      chunksGrade,List.map_cons,List.sum_cons,List.map_append,List.sum_append] using Nat.add_le_add (prepareChunk_grade A M w) ih

 theorem preprocess_grade (w : List (Letter S Γ Q)) :
    chunksGrade (preprocess A M w) ≤ grade w := by
  have h := prepareChunks_grade A M (Path.cuts w)
  simpa only [preprocess,Path.prepare,← chunksGrade_flatten,Path.flatten_cuts] using h

end

variable {S Γ Q : Type*} (blank : Γ)

def raw (w : List S) : List (Letter S Γ Q) := encode (Surface.raw blank w)

/-- Candidate extraction followed by a literal check recognizes *only* full,
    clean raw sectors. Dirty tags or absent boundaries cannot silently pass. -/
def rawLetters (w : List (Letter S Γ Q)) : List S := w.filterMap fun a =>
  match a with
  | .right (.anchor s,_) => some s
  | _ => none

@[simp] theorem rawLetters_raw (w : List S) : rawLetters (raw (Q := Q) blank w) = w := by
  simp [raw,encode,Scan.literal,Path.encode,Surface.raw,Path.headed,rawLetters,
    List.filterMap_append,List.filterMap_map,Validator.cell,Function.comp_def]

variable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

def readRaw (w : List (Letter S Γ Q)) : Option (List S) :=
  let x := rawLetters w
  if raw blank x = w then some x else none

@[simp] theorem readRaw_raw (w : List S) : readRaw blank (raw (Q := Q) blank w) = some w := by
  simp [readRaw]

 theorem readRaw_sound {w : List (Letter S Γ Q)} {x : List S} (h : readRaw blank w = some x) :
    raw blank x = w := by
  dsimp only [readRaw] at h
  split at h
  · cases h; assumption
  · cases h

abbrev Item (S Γ Q : Type*) := RawRuns.Item (List (Letter S Γ Q)) S

def classify (w : List (Letter S Γ Q)) : Item S Γ Q :=
  match readRaw blank w with
  | some x => .inr x
  | none => .inl w

def realize : Item S Γ Q → List (Letter S Γ Q)
  | .inl w => w
  | .inr x => raw blank x

@[simp] theorem classify_raw (w : List S) : classify blank (raw (Q := Q) blank w) = .inr w := by
  simp [classify]

@[simp] theorem realize_classify (w : List (Letter S Γ Q)) : realize blank (classify blank w) = w := by
  unfold classify
  cases he : readRaw blank w with
  | none => rfl
  | some x => exact readRaw_sound blank he

@[simp] theorem itemGrade_classify (w : List (Letter S Γ Q)) :
    RawRuns.itemGrade grade (classify blank w) = grade w := by
  unfold classify
  cases he : readRaw blank w with
  | none => rfl
  | some x => rw [←readRaw_sound blank he]; exact (grade_raw blank x).symm

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
@[simp] theorem grade_realize (w : Item S Γ Q) :
    grade (realize blank w) = RawRuns.itemGrade grade w := by
  cases w with
  | inl w => rfl
  | inr x => exact grade_raw blank x

@[simp] theorem classify_grade (ws : List (List (Letter S Γ Q))) :
    RawRuns.grade grade (ws.map (classify blank)) = chunksGrade ws := by
  simp only [RawRuns.grade,List.map_map,Function.comp_def,itemGrade_classify,chunksGrade]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
@[simp] theorem realizeList_grade (ws : List (Item S Γ Q)) :
    grade (ws.flatMap (realize blank)) = RawRuns.grade grade ws := by
  rw [List.flatMap_def,chunksGrade_flatten]
  simp only [chunksGrade,List.map_map,Function.comp_def,grade_realize,RawRuns.grade]

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Surface
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The exact exceptional comparison. When entry priority changes the answer,
    both boundaries really exist, and a bounded run of the specified machine
    returns the output of cleanup. No program equation is assumed here. -/
theorem exit_alternative
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (l : Cells S Γ) (lb : Bool) :
    preprocess A M ⟨l,.internal (.machine .ok),[],lb,true⟩ =
      preprocess A M ⟨l,.cleanup,[],lb,true⟩ ∨
    ∃ x y out n c,
      preprocess A M ⟨l,.internal (.machine .ok),[],lb,true⟩ =
        [raw A.blank x,raw A.blank y] ∧
      preprocess A M ⟨l,.cleanup,[],lb,true⟩ = [raw A.blank out] ∧
      ReflTransGen (Simulator.TapeStep M)
        (Simulator.pad A (Simulator.initialTape A M (x++y)) (n+1)) c ∧
      Simulator.Halted A M c ∧ Simulator.Returns A c out := by
  let v : Control.Sector S Γ Q := ⟨l,.machine .ok,[],lb,true⟩
  by_cases he : ∃ w, EqvGen (Scan.Step (Control.table A M)) v w ∧ Control.Entry A.blank w
  · obtain ⟨w,hw,hwe⟩ := he
    obtain ⟨a,ha,rfl⟩ := Control.entry_cases A.blank hwe
    have hc := Control.cfg_connected A M (EqvGen.symm _ _ hw)
    change EqvGen (Compiled.Step A M) (Control.toCfg (Control.validator a))
      (Control.toCfg (Control.machine ⟨l,.ok,[],lb,true⟩)) at hc
    rw [Control.cfg_validator,Control.cfg_machine] at hc
    obtain ⟨x,y,s,n,c,out,result,rfl,_,hr,hh,ho,_,hb,hclean⟩ :=
      Compiled.accepting_entry_sound A M hdecode ha rfl hc
    right
    refine ⟨x,y,out,n,c,?_,?_,hr,hh,ho⟩
    · change internalPreprocess A M v = _
      rw [internalPreprocess_invariant A M hw,
        internalPreprocess_entry A M _ (Control.entry_validator A.blank ha)]
      exact pendingPreprocess_cleanEntry A x y s
    · have hn := cleanupPreprocess_invariant (H := Control.Head S Q) A.blank
        (EqvGen.reflTransGen_le_eqvGen _ _ _ hclean)
      have he : (⟨l,.cleanup,[],lb,true⟩ : Cleanup.Sector S Γ) =
          ⟨result.reverse,.cleanup,[],true,true⟩ := by
        have h₁ := congrArg (fun v : Compiled.MachineSector S Γ Q => v.left) hb
        have h₂ := congrArg (fun v : Compiled.MachineSector S Γ Q => v.leftBoundary) hb
        simp only at h₁ h₂
        subst l; subst lb; rfl
      rw [←he] at hn
      change [cleanupPreprocess A.blank (ofCleanup ⟨l,.cleanup,[],lb,true⟩)] = _
      rw [hn]
      rfl
  · left
    exact internalPreprocess_success A M v ⟨rfl,rfl,rfl⟩ he

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The source algorithm, with the partial call separated as f. Its actual
    computable domain/realization is established at the program boundary. -/
def normal (f : List S → List S) (w : List (Letter S Γ Q)) : List (Letter S Γ Q) :=
  if Path.shape w = .zero then [.zero] else
    (RawRuns.source f ((preprocess A M w).map (classify A.blank))).flatMap (realize A.blank)

theorem normal_eq_fold {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m)
    (w : List (Letter S Γ Q)) (hn : Path.shape w ≠ .zero) (hm : grade w ≤ m) :
    normal A M f w =
      (RawRuns.normalize f ((preprocess A M w).map (classify A.blank))).flatMap (realize A.blank) := by
  rw [normal,ite_eq_right hn,RawRuns.source_eq_normalize grade h]
  exact (by rw [classify_grade]; exact (preprocess_grade A M w).trans hm)

theorem normal_grade {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) : grade (normal A M f w) ≤ grade w := by
  unfold normal
  split
  · simp [grade,Path.grade,Path.letterGrade]
  · rw [realizeList_grade]
    have hp := preprocess_grade A M w
    have hm' : RawRuns.grade grade ((preprocess A M w).map (classify A.blank)) ≤ m := by
      rw [classify_grade]; exact hp.trans hm
    exact (RawRuns.source_grade grade h _ hm').trans (by simpa using hp)

theorem normal_ordinary (f : List S → List S) {u v : List (Letter S Γ Q)}
    (h : Ordinary A M u v) (x y : List (Letter S Γ Q)) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have hs := Path.shape_context (ordinary_shape A M h) x y
  by_cases hn : Path.shape (x++u++y) = .zero
  · simp only [normal,hn,←hs,ite_eq_left]
  · simp only [normal,hn,←hs,ite_false,preprocess_ordinary A M h x y hn]

theorem normal_zero (f : List S → List S) {u v : List (Letter S Γ Q)}
    (h : Path.ZeroStep u v) (x y : List (Letter S Γ Q)) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have h₁ : Path.shape (x++u++y) = .zero := by
    cases h with
    | pair a b h => simp only [Path.shape_append,Path.shape_cons,Path.shape_nil,
        Path.mul_unit,h,Path.mul_zero,Path.zero_mul]
  have h₂ := Path.shape_context (rule_shape A M (.zero h)) x y
  simp only [normal,h₁,←h₂,ite_eq_left]

@[simp] theorem preprocess_raw (w : List S) : preprocess A M (raw (Q := Q) A.blank w) =
    [raw A.blank w] := by
  unfold preprocess raw encode Path.prepare Path.encode
  rw [Path.cuts_headed]
  change Path.prepareChunks (sectorPreprocess A M) [Path.encode (Scan.literal id (Surface.raw A.blank w))] = _
  rw [Path.prepareChunks_singleton,sectorPreprocess_literal]
  rfl

@[simp] theorem normal_raw (f : List S → List S) (w : List S) :
    normal A M f (raw (Q := Q) A.blank w) = raw A.blank w := by
  have hn : Path.shape (raw (Q := Q) A.blank w) ≠ .zero := by
    simp [raw,encode,Path.encode]
  simp [normal,hn,RawRuns.source,RawRuns.splitRun,realize]

/-- Finite tape realization at a bound. This is a *lemma parameter*, not an
    assumption of either main theorem; the partial-recursive adapter must prove it. -/
def ComputesAt (f : List S → List S) (m : ℕ) : Prop :=
  ∀ w, w.length ≤ m → ∃ c,
    ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M w) c ∧
    Simulator.Halted A M c ∧ Simulator.Returns A c (f w)

theorem normal_exit
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (a b : List (Letter S Γ Q))
    (h₁ : grade (a++[.head (.internal (.machine .ok)),.leave]++b) ≤ m)
    (h₂ : grade (a++[.head .cleanup,.leave]++b) ≤ m) :
    normal A M f (a++[.head (.internal (.machine .ok)),.leave]++b) =
      normal A M f (a++[.head .cleanup,.leave]++b) := by
  have hs := Path.shape_context (rule_shape A M .exit) a b
  by_cases hn : Path.shape (a++[.head (.internal (.machine .ok)),.leave]++b) = .zero
  · simp only [normal,hn,←hs,ite_eq_left]
  have hn₂ : Path.shape (a++[.head .cleanup,.leave]++b) ≠ .zero := by rwa [←hs]
  obtain ⟨cs,ds,l,lb,hframe⟩ := Path.right_boundary_frame a b (.internal (.machine .ok)) hn
  have hf : ∀ q : Head S Q, preprocess A M (a++[.head q,.leave]++b) =
      Path.prepareChunks (sectorPreprocess A M) cs ++
      (Surface.preprocess A M ⟨l,q,[],lb,true⟩).map encode ++
      Path.prepareChunks (sectorPreprocess A M) ds := by
    intro q
    simp only [preprocess,Path.prepare,hframe,Path.prepareChunks_append]
    change _ ++ Path.prepareChunks (sectorPreprocess A M) [Path.encode (Scan.literal id ⟨l,q,[],lb,true⟩)] ++ _ = _
    rw [Path.prepareChunks_singleton,sectorPreprocess_literal]
    simp only [List.map_map,Function.comp_def]
    rfl
  rcases Surface.exit_alternative A M hdecode l lb with he | ⟨x,y,out,n,c,hx,hy,hr,hh,ho⟩
  · simp only [normal,ite_eq_right hn,ite_eq_right hn₂,hf,he]
  · let p := (Path.prepareChunks (sectorPreprocess A M) cs).map (classify A.blank)
    let q := (Path.prepareChunks (sectorPreprocess A M) ds).map (classify A.blank)
    have hp : (preprocess A M (a++[.head (.internal (.machine .ok)),.leave]++b)).map
        (classify A.blank) = p ++ .inr x :: .inr y :: q := by
      simp only [hf,hx,List.map_cons,List.map_nil,List.map_append]
      change p ++ [classify A.blank (raw A.blank x),classify A.blank (raw A.blank y)] ++ q = _
      simp [List.append_assoc]
    have hq : (preprocess A M (a++[.head .cleanup,.leave]++b)).map (classify A.blank) =
        p ++ .inr out :: q := by
      simp only [hf,hy,List.map_cons,List.map_nil,List.map_append]
      change p ++ [classify A.blank (raw A.blank out)] ++ q = _
      simp [List.append_assoc]
    have hbound : RawRuns.grade grade (p ++ .inr x :: .inr y :: q) ≤ m := by
      rw [←hp,classify_grade]
      exact (preprocess_grade A M _).trans h₁
    have hlen : (x++y).length ≤ m := by
      simp only [RawRuns.grade_append,RawRuns.grade_cons,RawRuns.itemGrade,List.length_append] at hbound ⊢
      omega
    obtain ⟨d,hd,hdh,hdo⟩ := hcomp (x++y) hlen
    have hout : out = f (x++y) := Simulator.returned_quota_unique A M (n+1) hr hd hh hdh ho hdo
    rw [normal_eq_fold A M h _ hn h₁,normal_eq_fold A M h _ hn₂ h₂,hp,hq,hout]
    exact congrArg (fun z => z.flatMap (realize A.blank)) (RawRuns.pair_context grade h x y p q hbound)

/-- Every literal defining equation is invariant in arbitrary word contexts,
    including dirty and incomplete sectors, within the *unchanged* grade bound. -/
theorem normal_rule
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Rule A M u v) (a b : List (Letter S Γ Q))
    (h₁ : grade (a++u++b) ≤ m) (h₂ : grade (a++v++b) ≤ m) :
    normal A M f (a++u++b) = normal A M f (a++v++b) := by
  cases hr with
  | zero hr => exact normal_zero A M f hr a b
  | ordinary hr => exact normal_ordinary A M f hr a b
  | exit => exact normal_exit A M hdecode h hcomp a b h₁ h₂

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H : Type*}

theorem context_headed {R : List (Letter C H) → List (Letter C H) → Prop}
    {l₁ l₂ r₁ r₂ : List C} {q₁ q₂ : H}
    (h : R (headed l₁ q₁ r₁ false false) (headed l₂ q₂ r₂ false false))
    (l r : List C) (lb rb : Bool) :
    Context R (headed (l₁++l) q₁ (r₁++r) lb rb)
      (headed (l₂++l) q₂ (r₂++r) lb rb) := by
  have hh := Context.apply ((if lb then [.enter] else []) ++ l.reverse.map .left)
      (r.map .right ++ (if rb then [.leave] else [])) h
  simp only [headed,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
    List.reverse_append,List.map_append,List.append_assoc] at hh ⊢
  exact hh

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {H B T K : Type*}

theorem encode_step (table : Table H B T) (m : H → K) {v w : Sector H B T}
    (h : Step table v w) :
    Context (Rule table m) (Path.encode (literal m v)) (Path.encode (literal m w)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  unfold Step step at h
  cases hd : table.direction q <;> simp only [hd] at h
  · cases l with
    | nil =>
      cases lb <;> simp only [Bool.false_eq_true,↓reduceIte] at h
      · contradiction
      · obtain ⟨q',hq,rfl⟩ := Option.map_eq_some_iff.mp h
        have hh := Context.apply [] (r.map .right++(if rb then [.leave] else []))
          (Rule.left (table := table) (m := m) q q' hd hq)
        simp only [Path.encode,literal,headed,List.nil_append,List.append_nil,
          List.map_nil,List.reverse_nil,ite_true,List.singleton_append,List.append_assoc] at hh ⊢
        exact hh
    | cons c l =>
      rcases c with ⟨b,t⟩
      obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp h
      have hh := context_headed (Rule.cell (table := table) (m := m) q b t i hi) l r lb rb
      cases hc : i.cross <;>
        simpa [Path.encode,literal,inLeft,inRight,outLeft,outRight,hd,hc] using hh
  · cases r with
    | nil =>
      cases rb <;> simp only [Bool.false_eq_true,↓reduceIte] at h
      · contradiction
      · obtain ⟨q',hq,rfl⟩ := Option.map_eq_some_iff.mp h
        have hh := Context.apply ((if lb then [.enter] else [])++l.reverse.map .left) []
          (Rule.right (table := table) (m := m) q q' hd hq)
        simp only [Path.encode,literal,headed,List.append_nil,
          List.map_nil,ite_true,List.append_assoc] at hh ⊢
        exact hh
    | cons c r =>
      rcases c with ⟨b,t⟩
      obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp h
      have hh := context_headed (Rule.cell (table := table) (m := m) q b t i hi) l r lb rb
      cases hc : i.cross <;>
        simpa [Path.encode,literal,inLeft,inRight,outLeft,outRight,hd,hc] using hh

end FiniteAlgebraicEnvelopes.Compiler.Scan.Literal

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

/-- A literal equation in either direction, used without any grade increase. -/
def Reduce (u v : List (Letter S Γ Q)) : Prop :=
  Path.Context (SymmGen (Rule A M)) u v ∧ grade v ≤ grade u
abbrev Reduces := ReflTransGen (Reduce A M)

theorem reduces_grade {u v : List (Letter S Γ Q)} (h : Reduces A M u v) : grade v ≤ grade u := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact h.2.trans ih

theorem reduce_context {u v : List (Letter S Γ Q)} (h : Reduce A M u v)
    (x y : List (Letter S Γ Q)) : Reduce A M (x++u++y) (x++v++y) := by
  refine ⟨Path.context_context h.1 x y,?_⟩
  simpa only [grade_append] using Nat.add_le_add_right (Nat.add_le_add_left h.2 (grade x)) (grade y)

theorem reduces_context {u v : List (Letter S Γ Q)} (h : Reduces A M u v)
    (x y : List (Letter S Γ Q)) : Reduces A M (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ hh => reduce_context A M hh x y)

theorem reduces_append {u v x y : List (Letter S Γ Q)}
    (h₁ : Reduces A M u v) (h₂ : Reduces A M x y) : Reduces A M (u++x) (v++y) := by
  have ha : Reduces A M (u++x) (v++x) := by simpa using reduces_context A M h₁ [] x
  have hb : Reduces A M (v++x) (v++y) := by simpa using reduces_context A M h₂ v []
  exact ha.trans hb

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

theorem normal_reduce
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Reduce A M u v) (hm : grade u ≤ m) :
    normal A M f u = normal A M f v := by
  have hv := hr.2.trans hm
  rcases hr with ⟨hr,_⟩
  cases hr with
  | apply x y hr =>
    rcases hr with hr | hr
    · exact normal_rule A M hdecode h hcomp hr x y hm hv
    · exact (normal_rule A M hdecode h hcomp hr x y hv hm).symm

theorem normal_reduces
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Reduces A M u v) (hm : grade u ≤ m) :
    normal A M f u = normal A M f v := by
  induction hr with
  | refl => rfl
  | tail hp hs ih => exact ih.trans (normal_reduce A M hdecode h hcomp hs ((reduces_grade A M hp).trans hm))

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H : Type*}

theorem context_mono {R T : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context R u v) (ht : ∀ a b, R a b → T a b) : Context T u v := by
  cases h with
  | apply x y h => exact .apply x y (ht _ _ h)

open Relation
theorem context_symm {R : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context (SymmGen R) u v) : Context (SymmGen R) v u := by
  cases h with
  | apply x y h => exact .apply x y (Or.symm h)

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem internal_rule_grade {u v : List (Letter S Γ Q)}
    (h : Scan.Literal.Rule (Control.table A M) Surface.Head.internal u v) : grade u = grade v := by
  cases h with
  | cell q b t i hi =>
    cases hd : (Control.table A M).direction q <;> cases hc : i.cross <;>
      simp [grade,Path.grade_headed,Scan.Literal.inLeft,Scan.Literal.inRight,
        Scan.Literal.outLeft,Scan.Literal.outRight,gradeCell,Nat.add_comm]
  | left => rfl
  | right => rfl

theorem ordinary_grade {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) : grade v ≤ grade u := by
  cases h with
  | internal h => exact (internal_rule_grade A M h).symm.le
  | clean c =>
    have hh := Cleanup.output_grade_le A.blank [c]
    simp only [Cleanup.output_singleton,Cleanup.cellsGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Nat.add_zero,Function.comp_def] at hh
    simpa [grade,Path.grade,Path.letterGrade,List.map_map,Function.comp_def,gradeCell,Nat.add_comm] using Nat.add_le_add_left hh 1
  | raw | merge | quota | entry | finish =>
    simp [grade,Path.grade,Path.letterGrade,gradeCell,Validator.cell,Cleanup.grade]

theorem rule_grade {u v : List (Letter S Γ Q)} (h : Rule A M u v) : grade v ≤ grade u := by
  cases h with
  | ordinary h => exact ordinary_grade A M h
  | zero h => exact Path.zeroStep_grade gradeCell h
  | exit => rfl

theorem reduce_rule {u v : List (Letter S Γ Q)} (h : Rule A M u v) : Reduce A M u v := by
  refine ⟨?_,rule_grade A M h⟩
  simpa using Path.Context.apply [] [] (Or.inl h : SymmGen (Rule A M) u v)

theorem reduce_rule_reverse {u v : List (Letter S Γ Q)} (h : Rule A M u v)
    (hg : grade u = grade v) : Reduce A M v u := by
  refine ⟨?_,hg.le⟩
  simpa using Path.Context.apply [] [] (Or.inr h : SymmGen (Rule A M) v u)

theorem reduce_internal {v w : Control.Sector S Γ Q} (h : Scan.Step (Control.table A M) v w) :
    Reduce A M (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) ∧
    Reduce A M (encode (Scan.mapHead Surface.Head.internal w))
      (encode (Scan.mapHead Surface.Head.internal v)) := by
  have hc := Scan.Literal.encode_step (Control.table A M) Surface.Head.internal h
  have hg : grade (encode (Scan.mapHead Surface.Head.internal v)) =
      grade (encode (Scan.mapHead Surface.Head.internal w)) := by
    rw [grade_encode,grade_encode]
    apply Surface.grade_eq_of_skeleton
    simpa using Scan.step_skeleton _ h
  have hf : Path.Context (SymmGen (Rule A M)) (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) :=
    Path.context_mono hc (fun _ _ hs => .inl (.ordinary (.internal hs)))
  refine ⟨⟨hf,hg.symm.le⟩,⟨?_,hg.le⟩⟩
  exact Path.context_symm hf

theorem reduces_internal {v w : Control.Sector S Γ Q}
    (h : EqvGen (Scan.Step (Control.table A M)) v w) :
    Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) := by
  have hh : ∀ {v w : Control.Sector S Γ Q}, EqvGen (Scan.Step (Control.table A M)) v w →
      Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
        (encode (Scan.mapHead Surface.Head.internal w)) ∧
      Reduces A M (encode (Scan.mapHead Surface.Head.internal w))
        (encode (Scan.mapHead Surface.Head.internal v)) := by
    intro v w h
    induction h with
    | rel _ _ h => exact ⟨.single (reduce_internal A M h).1,.single (reduce_internal A M h).2⟩
    | refl _ => exact ⟨.refl,.refl⟩
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1,ih₂.2.trans ih₁.2⟩
  exact (hh h).1

theorem reduce_of_context_rule {u v : List (Letter S Γ Q)} (h : Path.Context (Rule A M) u v) :
    Reduce A M u v := by
  refine ⟨Path.context_mono h (fun _ _ hh => .inl hh),?_⟩
  cases h with
  | apply x y h =>
    simp only [grade_append]
    exact Nat.add_le_add_right (Nat.add_le_add_left (rule_grade A M h) _) _

theorem reduce_reverse {u v : List (Letter S Γ Q)} (h : Reduce A M u v)
    (hg : grade u = grade v) : Reduce A M v u := ⟨Path.context_symm h.1,hg.le⟩

theorem reduces_reverse {u v : List (Letter S Γ Q)} (h : Reduces A M u v)
    (hg : grade u = grade v) : Reduces A M v u := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    have h₁ := reduces_grade A M hp
    have h₂ := hs.2
    have he : grade u = grade v := by omega
    have he' : grade v = grade w := by omega
    exact (ReflTransGen.single (reduce_reverse A M hs he')).trans (ih he)

theorem reduce_headed {l₁ l₂ r₁ r₂ : List (Cell S Γ)} {q₁ q₂ : Head S Q}
    (h : Rule A M (Path.headed l₁ q₁ r₁ false false) (Path.headed l₂ q₂ r₂ false false))
    (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨l₁++l,q₁,r₁++r,lb,rb⟩) (encode ⟨l₂++l,q₂,r₂++r,lb,rb⟩) :=
  reduce_of_context_rule A M (Path.context_headed h l r lb rb)

theorem reduce_rawStep {v w : Surface.Sector S Γ (Control.Head S Q)}
    (h : Surface.RawStep A.blank v w) : Reduce A M (encode v) (encode w) := by
  cases h with
  | slide a l r lb rb =>
    apply reduce_headed A M (l₁ := [Validator.cell A.blank (.anchor a)]) (l₂ := [])
      (r₁ := []) (r₂ := [Validator.cell A.blank (.anchor a)]) ?_ l r lb rb
    simpa [Path.headed] using (Rule.ordinary (Ordinary.raw (A := A) (M := M) a))

theorem reduces_rawNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.rawNormal A.blank v)) :=
  (Surface.rawNormal_reaches A.blank v).lift encode (fun _ _ h => reduce_rawStep A M h)

theorem reduces_quotaNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.quotaNormal A.blank v)) := by
  apply (Surface.quotaNormal_reaches A.blank v).lift encode
  intro v w h
  cases h with
  | trim l r lb rb =>
    apply reduce_headed A M (l₁ := [Validator.cell A.blank .workspace]) (l₂ := [])
      (r₁ := [Validator.cell A.blank .cutD]) (r₂ := [Validator.cell A.blank .cutD]) ?_ l r lb rb
    simpa [Path.headed] using (Rule.ordinary (Ordinary.quota (A := A) (M := M)))

theorem reduce_entry (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩)
      (encode ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩) := by
  apply reduce_headed A M (l₁ := []) (l₂ := [])
    (r₁ := [Validator.cell A.blank .cutD]) (r₂ := [Validator.cell A.blank .cutD]) ?_ l r lb rb
  simpa [Path.headed] using (Rule.ordinary (Ordinary.entry (A := A) (M := M)))

theorem reduce_cleanup {v w : Cleanup.Sector S Γ} (h : Cleanup.Step A.blank v w) :
    Reduce A M (encode (Surface.ofCleanup v)) (encode (Surface.ofCleanup w)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw => cases h
  | cleanup =>
    cases l with
    | nil =>
      cases lb with
      | false => cases h
      | true =>
        cases Option.some.inj h
        apply reduce_of_context_rule A M
        have hh := Path.Context.apply [] (r.map .right++(if rb then [.leave] else []))
            (Rule.ordinary (Ordinary.finish (A := A) (M := M)))
        simp only [encode,Scan.literal,Path.encode,Path.headed,Surface.ofCleanup,Scan.mapHead,Surface.cleanupHead,
          List.map_nil,List.reverse_nil,List.nil_append,List.append_nil,ite_true,
          List.singleton_append,List.append_assoc] at hh ⊢
        exact hh
    | cons c l =>
      cases Option.some.inj h
      apply reduce_headed A M (l₁ := [c]) (l₂ := []) (r₁ := [])
        (r₂ := (Cleanup.emit c).toList.map (Cleanup.letter A.blank)) ?_ l r lb rb
      simpa only [Surface.cleanupHead,Path.headed,List.map_nil,List.nil_append,List.map_cons,
        List.reverse_cons,List.reverse_nil,List.append_nil,List.singleton_append,Bool.false_eq_true,ite_false] using
          (Rule.ordinary (Ordinary.clean (A := A) (M := M) c))

theorem reduces_cleanupNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.cleanupNormal A.blank v)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | cleanup =>
    exact (Cleanup.normal_reached A.blank ⟨l,.cleanup,r,lb,rb⟩).lift
      (fun v => encode (Surface.ofCleanup v)) (fun _ _ h => reduce_cleanup A M h)
  | raw | pending | internal _ => exact .refl

theorem reduces_cleanupPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.cleanupPreprocess A.blank v)) :=
  (reduces_cleanupNormal A M v).trans (reduces_rawNormal A M _)

theorem reduce_unmerge (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨Validator.cell A.blank .cutC::l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩)
      (encode ⟨l,.raw,[],lb,true⟩ ++ encode ⟨[],.raw,r,true,rb⟩) := by
  have hr := reduce_rule_reverse A M (.ordinary .merge) (by
    simp [grade,Path.grade,Path.letterGrade,gradeCell,Validator.cell,Cleanup.grade])
  have hh := reduce_context A M hr ((if lb then [.enter] else [])++l.reverse.map .left)
      (r.map .right++(if rb then [.leave] else []))
  simp only [encode,Scan.literal,Path.encode,Path.headed,List.reverse_cons,List.reverse_nil,
    List.map_cons,List.map_append,List.map_nil,List.append_nil,
    List.singleton_append,ite_true,List.append_assoc] at hh ⊢
  exact hh

theorem reduces_unmerge (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.unmerge A.blank v).flatMap encode) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l with
  | nil =>
    simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
  | cons c l =>
    cases q with
    | raw | cleanup | internal _ =>
      simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
    | pending =>
      cases r with
      | nil =>
        simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
      | cons d r =>
        by_cases h : c = Validator.cell A.blank .cutC ∧ d = Validator.cell A.blank .cutD
        · rcases h with ⟨rfl,rfl⟩
          have hp := (reduces_rawNormal A M ⟨l,.raw,[],lb,true⟩)
          have hq := (reduces_rawNormal A M ⟨[],.raw,r,true,rb⟩)
          simpa [Surface.unmerge] using
            ((ReflTransGen.single (reduce_unmerge A M l r lb rb)).trans (reduces_append A M hp hq))
        · simpa only [Surface.unmerge,ite_eq_right h,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
            (ReflTransGen.refl (a := encode ⟨c::l,.pending,d::r,lb,rb⟩) : Reduces A M _ _)

theorem reduces_pendingPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.pendingPreprocess A.blank v).flatMap encode) :=
  (reduces_quotaNormal A M v).trans (reduces_unmerge A M _)

theorem reduce_exit (l : List (Cell S Γ)) (lb : Bool) :
    Reduce A M (encode ⟨l,.internal (.machine .ok),[],lb,true⟩)
      (encode ⟨l,.cleanup,[],lb,true⟩) := by
  have hh := reduce_context A M (reduce_rule A M .exit) ((if lb then [.enter] else [])++l.reverse.map .left) []
  simp only [encode,Scan.literal,Path.encode,Path.headed,List.map_nil,List.append_nil,
    ite_true,List.append_assoc] at hh ⊢
  exact hh

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

theorem reduces_internalPreprocess (v : Control.Sector S Γ Q) :
    Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
      ((Surface.internalPreprocess A M v).flatMap encode) := by
  have hp := reduces_internal A M (Control.representative_connected A M v)
  refine hp.trans ?_
  generalize hw : Control.representative A M v = w at *
  rcases w with ⟨l,q,r,lb,rb⟩
  unfold Surface.internalPreprocess
  rw [hw]
  dsimp only
  by_cases he : Control.Entry A.blank ⟨l,q,r,lb,rb⟩
  · rw [ite_eq_left he]
    rcases he with ⟨rfl,hr⟩
    cases r with
    | nil => cases hr
    | cons c r =>
      cases Option.some.inj hr
      have hh := reduce_entry A M l r lb rb
      have hg : grade (Q := Q) (encode ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩) =
          grade (Q := Q) (encode ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩) := by
        rw [grade_encode,grade_encode]; rfl
      exact (ReflTransGen.single (reduce_reverse A M hh hg)).trans (reduces_pendingPreprocess A M _)
  · rw [ite_eq_right he]
    by_cases hs : Control.Success ⟨l,q,r,lb,rb⟩
    · rw [ite_eq_left hs]
      rcases hs with ⟨rfl,rfl,rfl⟩
      simpa only [Scan.mapHead,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
        ((ReflTransGen.single (reduce_exit A M l lb)).trans (reduces_cleanupPreprocess A M _))
    · rw [ite_eq_right hs]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
      exact .refl

theorem reduces_sectorPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.preprocess A M v).flatMap encode) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw =>
    simpa only [Surface.preprocess,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      reduces_rawNormal A M ⟨l,.raw,r,lb,rb⟩
  | pending => exact reduces_pendingPreprocess A M _
  | cleanup =>
    simpa only [Surface.preprocess,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      reduces_cleanupPreprocess A M ⟨l,.cleanup,r,lb,rb⟩
  | internal q => exact reduces_internalPreprocess A M ⟨l,q,r,lb,rb⟩

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem reduces_prepareChunk (w : List (Letter S Γ Q)) :
    Reduces A M w (Path.prepareChunk (sectorPreprocess A M) w).flatten := by
  cases hd : Path.decode w with
  | none => simp only [Path.prepareChunk,hd,List.flatten_cons,List.flatten_nil,List.append_nil]; exact .refl
  | some v =>
    have hw := Path.decode_sound hd
    subst w
    have hh := reduces_sectorPreprocess A M (Scan.unliteral v)
    simp only [Path.prepareChunk_encode,sectorPreprocess,List.map_map,List.flatMap_def,
      Function.comp_def,encode,Scan.literal_unliteral] at hh ⊢
    exact hh

theorem reduces_prepareChunks (cs : List (List (Letter S Γ Q))) :
    Reduces A M cs.flatten (Path.prepareChunks (sectorPreprocess A M) cs).flatten := by
  induction cs with
  | nil => exact .refl
  | cons c cs ih =>
    simpa only [Path.prepareChunks,List.flatMap_cons,List.flatten_cons,List.flatten_append] using
      reduces_append A M (reduces_prepareChunk A M c) ih

theorem reduces_preprocess (w : List (Letter S Γ Q)) :
    Reduces A M w (preprocess A M w).flatten := by
  simpa only [preprocess,Path.prepare,Path.flatten_cuts] using reduces_prepareChunks A M (Path.cuts w)

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
 theorem reduces_zero {w : List (Letter S Γ Q)} (h : Path.shape w = .zero) :
    Reduces A M w [.zero] := by
  exact ReflTransGen.mono (fun _ _ hs =>
    reduce_of_context_rule A M (Path.context_mono hs (fun _ _ hh => .zero hh))) _ _ (Path.zero_reaches h)

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

omit [DecidableEq S] [DecidableEq Γ] in
theorem grade_flatMap_encode (vs : List (Surface.Sector S Γ (Control.Head S Q))) :
    grade (vs.flatMap encode) = Surface.listGrade vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.flatMap_cons,grade_append,grade_encode,ih,Surface.listGrade,
      List.map_cons,List.sum_cons]

theorem reduces_rawPair_of_run (x y out : List S)
    (c : Simulator.Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M (x++y)) c)
    (hhalt : Simulator.Halted A M c) (hout : Simulator.Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    Reduces A M (raw A.blank x ++ raw A.blank y) (raw A.blank out) := by
  obtain ⟨s,result,hr,hclean⟩ := Compiled.clean_success A M x y out c hrun hhalt hout hlen
  let e : Surface.Sector S Γ (Control.Head S Q) :=
    ⟨(Compiled.cleanEntry A.blank x y s).left,.pending,
      (Compiled.cleanEntry A.blank x y s).right,true,true⟩
  have he : (Surface.pendingPreprocess A.blank e).flatMap encode = raw A.blank x++raw A.blank y := by
    rw [show Surface.pendingPreprocess A.blank e = [Surface.raw A.blank x,Surface.raw A.blank y] from
      Surface.pendingPreprocess_cleanEntry A x y s]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,raw]
  have hp := reduces_pendingPreprocess A M e
  have hg : grade (encode e) = grade ((Surface.pendingPreprocess A.blank e).flatMap encode) := by
    rw [grade_encode,grade_flatMap_encode,Surface.pendingPreprocess_grade]
  have hp' := reduces_reverse A M hp hg
  rw [he] at hp'
  have hentry : Reduce A M (encode e)
      (encode (Scan.mapHead Surface.Head.internal (Control.validator (Compiled.cleanEntry A.blank x y s)))) :=
    reduce_entry A M _ _ true true
  have hrun' := reduces_internal A M (EqvGen.reflTransGen_le_eqvGen _ _ _ (Control.ofCfg_runs A M hr))
  simp only [Control.ofCfg] at hrun'
  have hc : Reduces A M (encode (Surface.ofCleanup ⟨result.reverse,.cleanup,[],true,true⟩))
      (raw A.blank out) := by
    exact hclean.lift (fun v => encode (Surface.ofCleanup v)) (fun _ _ hh => reduce_cleanup A M hh)
  exact hp'.trans ((ReflTransGen.single hentry).trans
    (hrun'.trans ((ReflTransGen.single (reduce_exit A M result.reverse true)).trans hc)))

theorem reduces_rawPair {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (x y : List S) (hm : (x++y).length ≤ m) :
    Reduces A M (raw A.blank x++raw A.blank y) (raw A.blank (f (x++y))) := by
  obtain ⟨c,hc,hh,ho⟩ := hcomp (x++y) hm
  exact reduces_rawPair_of_run A M x y (f (x++y)) c hc hh ho (by simpa using h.length (x++y) hm)

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

omit [DecidableEq Q] in
 theorem reduces_prepend {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (a : Item S Γ Q) (w : List (Item S Γ Q))
    (hm : RawRuns.itemGrade grade a + RawRuns.grade grade w ≤ m) :
    Reduces A M (realize A.blank a ++ w.flatMap (realize A.blank))
      ((RawRuns.prepend f a w).flatMap (realize A.blank)) := by
  cases a with
  | inl c => exact .refl
  | inr x =>
    cases w with
    | nil => exact .refl
    | cons a w =>
      cases a with
      | inl c => exact .refl
      | inr y =>
        have hl : (x++y).length ≤ m := by
          simp only [RawRuns.itemGrade,RawRuns.grade_cons,List.length_append] at *
          omega
        have hp := reduces_context A M (reduces_rawPair A M h hcomp x y hl) [] (w.flatMap (realize A.blank))
        simpa only [List.nil_append,List.flatMap_cons,RawRuns.prepend,realize,List.append_assoc] using hp

omit [DecidableEq Q] in
 theorem reduces_rawRuns {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Item S Γ Q)) (hm : RawRuns.grade grade w ≤ m) :
    Reduces A M (w.flatMap (realize A.blank))
      ((RawRuns.normalize f w).flatMap (realize A.blank)) := by
  induction w with
  | nil => exact .refl
  | cons a w ih =>
    have hb : RawRuns.grade grade w ≤ m := by simp only [RawRuns.grade_cons] at hm; omega
    have hp := reduces_append A M (ReflTransGen.refl (a := realize A.blank a)) (ih hb)
    have hg := RawRuns.normalize_grade grade h w hb
    have hh := reduces_prepend A M h hcomp a (RawRuns.normalize f w)
      (by simp only [RawRuns.grade_cons] at hm; omega)
    exact hp.trans hh

variable [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- A literal, grade-nonincreasing derivation to the source's whole-word
    evaluator, not just equality in an assumed quotient. -/
 theorem reduces_normal {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) :
    Reduces A M w (normal A M f w) := by
  by_cases hn : Path.shape w = .zero
  · simpa only [normal,ite_eq_left hn] using reduces_zero A M hn
  · rw [normal_eq_fold A M h w hn hm]
    have hp := reduces_preprocess A M w
    have hh := reduces_rawRuns A M h hcomp ((preprocess A M w).map (classify A.blank))
      (by rw [classify_grade]; exact (preprocess_grade A M w).trans hm)
    have hj : ((preprocess A M w).map (classify A.blank)).flatMap (realize A.blank) =
        (preprocess A M w).flatten := by
      simp only [List.flatMap_def,List.map_map,Function.comp_def,realize_classify,List.map_id']
    rw [hj] at hh
    exact hp.trans hh

 theorem normal_idempotent
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) :
    normal A M f (normal A M f w) = normal A M f w :=
  (normal_reduces A M hdecode h hcomp (reduces_normal A M h hcomp w hm) hm).symm

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The bounded context conclusion uses the nonincreasing literal derivations;
    the attachment need not preserve sector boundaries. -/
theorem normal_context
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (he : normal A M f u = normal A M f v)
    (x y : List (Letter S Γ Q))
    (hu : grade (x++u++y) ≤ m) (hv : grade (x++v++y) ≤ m) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have hu' : grade u ≤ m := by simp only [grade_append] at hu; omega
  have hv' : grade v ≤ m := by simp only [grade_append] at hv; omega
  have hp := normal_reduces A M hdecode h hcomp
    (reduces_context A M (reduces_normal A M h hcomp u hu') x y) hu
  have hq := normal_reduces A M hdecode h hcomp
    (reduces_context A M (reduces_normal A M h hcomp v hv') x y) hv
  rw [he] at hp
  exact hp.trans hq.symm

/-- The compiler's finite monoid presentation is formed from the literal rule
    table; neither a normalizer nor program totality enters its definition. -/
abbrev Rel (u v : FreeMonoid (Letter S Γ Q)) : Prop := Rule A M u v
abbrev Presentation := PresentedMonoid (Rel A M)
def present (w : List (Letter S Γ Q)) : Presentation A M := PresentedMonoid.mk (Rel A M) w

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_append (u v : List (Letter S Γ Q)) :
    present A M (u++v) = present A M u * present A M v := rfl

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_context {u v : List (Letter S Γ Q)} (he : present A M u = present A M v)
    (x y : List (Letter S Γ Q)) : present A M (x++u++y) = present A M (x++v++y) := by
  simp only [present_append,he]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_reduce {u v : List (Letter S Γ Q)} (h : Reduce A M u v) :
    present A M u = present A M v := by
  cases h.1 with
  | apply x y hr =>
    apply present_context A M ?_ x y
    rcases hr with hr | hr
    · exact PresentedMonoid.mk_eq_mk_of_rel hr
    · exact (PresentedMonoid.mk_eq_mk_of_rel hr).symm

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_reduces {u v : List (Letter S Γ Q)} (h : Reduces A M u v) :
    present A M u = present A M v := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (present_reduce A M h)

theorem present_normal {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) :
    present A M w = present A M (normal A M f w) :=
  present_reduces A M (reduces_normal A M h hcomp w hm)

/-- No maximum grade of a presentation derivation is assumed. Its finitely many
    contextual uses are handled by the theorem at all finite budgets. -/
theorem normal_conGen
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} (h : ∀ m, RawRuns.Budget f m) (hcomp : ∀ m, ComputesAt A M f m)
    {u v : FreeMonoid (Letter S Γ Q)} (he : conGen (Rel A M) u v) :
    normal A M f u = normal A M f v := by
  induction he with
  | of u v hr =>
    change Rule A M u.toList v.toList at hr
    change normal A M f u.toList = normal A M f v.toList
    have hp := normal_rule A M hdecode (h (max (grade u.toList) (grade v.toList)))
      (hcomp (max (grade u.toList) (grade v.toList))) hr [] []
      (by simpa only [List.nil_append,List.append_nil] using le_max_left (grade u.toList) (grade v.toList))
      (by simpa only [List.nil_append,List.append_nil] using le_max_right (grade u.toList) (grade v.toList))
    simpa only [List.nil_append,List.append_nil] using hp
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | @mul w x y z _ _ ih ij =>
    change normal A M f (w.toList++y.toList) = normal A M f (x.toList++z.toList)
    change normal A M f w.toList = normal A M f x.toList at ih
    change normal A M f y.toList = normal A M f z.toList at ij
    have hp := normal_context A M hdecode
      (h (max (grade (w.toList++y.toList)) (grade (x.toList++y.toList))))
      (hcomp (max (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))) ih [] y.toList
      (by simpa only [List.nil_append] using le_max_left (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))
      (by simpa only [List.nil_append] using le_max_right (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))
    have hq := normal_context A M hdecode
      (h (max (grade (x.toList++y.toList)) (grade (x.toList++z.toList))))
      (hcomp (max (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))) ij x.toList []
      (by simpa only [List.append_nil] using le_max_left (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))
      (by simpa only [List.append_nil] using le_max_right (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))
    simp only [List.nil_append,List.append_nil] at hp hq
    exact hp.trans hq

/-- Exact equality criterion for the finite presentation under the global
    (not assumed for constructing the presentation) evaluator hypotheses. -/
theorem present_eq_iff_normal
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} (h : ∀ m, RawRuns.Budget f m) (hcomp : ∀ m, ComputesAt A M f m)
    (u v : List (Letter S Γ Q)) :
    present A M u = present A M v ↔ normal A M f u = normal A M f v := by
  constructor
  · intro he
    exact normal_conGen A M hdecode h hcomp (PresentedMonoid.mk_eq_mk_iff.mp he)
  · intro he
    rw [present_normal A M (h (grade u)) (hcomp (grade u)) u le_rfl,
      present_normal A M (h (grade v)) (hcomp (grade v)) v le_rfl,he]

end

open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

@[simp] theorem normal_nil (f : List S → List S) : normal A M f [] = [] := by
  simp [normal,preprocess,Path.prepare,Path.prepareChunks,RawRuns.source]

@[simp] theorem normal_omega (f : List S → List S) :
    normal A M f [.zero] = [.zero] := by simp [normal,Path.typeOf]

theorem normal_contains_omega (f : List S → List S) (x y : List (Letter S Γ Q)) :
    normal A M f (x ++ .zero::y) = [.zero] := by
  rw [normal,ite_eq_left (Path.shape_zero_context x y)]

@[simp] theorem preprocess_raw_pair (u v : List S) :
    preprocess A M (raw (Q := Q) A.blank u ++ raw A.blank v) =
      [raw A.blank u,raw A.blank v] := by
  have hr (w : List S) : raw (Q := Q) A.blank w =
      [.enter,.head .raw] ++ (w.map (Validator.cell A.blank ∘ Base.anchor)).map Path.Letter.right ++ [.leave] := by
    simp [raw,encode,Surface.raw,Scan.literal,Path.encode,Path.headed]
  have hc : Path.cuts (raw (Q := Q) A.blank u ++ raw A.blank v) =
      Path.cuts (raw A.blank u) ++ Path.cuts (raw A.blank v) := by
    rw [hr u]
    rw [List.append_assoc, List.singleton_append, Path.cuts_append_leave]
  unfold preprocess Path.prepare
  rw [hc]
  change Path.prepareChunks (sectorPreprocess A M)
    (Path.cuts (raw A.blank u) ++ Path.cuts (raw A.blank v)) = _
  rw [Path.prepareChunks_append]
  exact congrArg₂ List.append (preprocess_raw A M u) (preprocess_raw A M v)

/-- Singleton raw words are fixed, but adjacent full raw words call the program
    on their concatenation, exactly as in the manuscript. -/
theorem normal_raw_product (f : List S → List S) (u v : List S) :
    normal A M f (raw (Q := Q) A.blank u ++ raw A.blank v) = raw A.blank (f (u++v)) := by
  have hn : Path.shape (raw (Q := Q) A.blank u ++ raw A.blank v) ≠ .zero := by
    simp [raw,encode,Path.encode,Path.path_mul_path,Surface.raw,Scan.literal]
  rw [normal,ite_eq_right hn]
  simp [RawRuns.source,RawRuns.splitRun,realize]

theorem present_nil_ne_omega
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} (h : ∀ m, RawRuns.Budget f m) (hcomp : ∀ m, ComputesAt A M f m) :
    present A M [] ≠ present A M [.zero] := by
  intro he
  have hh := (present_eq_iff_normal A M hdecode h hcomp [] [.zero]).mp he
  simp at hh

end FiniteAlgebraicEnvelopes.Compiler.Word

/- The actual partial evaluator is a finite plan followed by partial calls.
   Its definition has no budget and does not totalize an undefined program. -/
namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

/-- A nonraw literal sector, an unchanged singleton raw sector, or a genuine
    program call on an entire maximal raw run. -/
inductive Action (C S : Type*)
  | keep (c : C)
  | raw (w : List S)
  | call (w : List S)
  deriving DecidableEq

def plan : List (Item C S) → List (Action C S)
  | [] => []
  | .inl c::w => .keep c::plan w
  | .inr x::w =>
    let p := splitRun w
    let z := match p.1 with
      | [] => Action.raw x
      | _::_ => Action.call (x++p.1.flatten)
    z :: plan p.2
termination_by w => w.length
decreasing_by
  · simp_wf
  · have := splitRun_length w
    simp_wf
    omega

def Action.total (f : List S → List S) : Action C S → Item C S
  | .keep c => .inl c
  | .raw x => .inr x
  | .call x => .inr (f x)

theorem plan_total (f : List S → List S) (w : List (Item C S)) :
    (plan w).map (Action.total f) = source f w := by
  cases w with
  | nil => simp [plan,source]
  | cons a w =>
    cases a with
    | inl c => simp only [plan,source,List.map_cons,Action.total,plan_total f w]
    | inr x =>
      have ht := splitRun_length w
      rw [plan,source,List.map_cons,plan_total f (splitRun w).2]
      cases (splitRun w).1 <;> rfl
termination_by w.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- Every program argument is bounded by the grade of the original item list,
    before any output from the program is computed. -/
theorem plan_call_bound (g : C → ℕ) (w : List (Item C S)) {x : List S}
    (hx : Action.call x ∈ plan w) : x.length ≤ grade g w := by
  cases w with
  | nil => simp [plan] at hx
  | cons a w =>
    cases a with
    | inl c =>
      simp only [plan,List.mem_cons] at hx
      rcases hx with he | hx
      · cases he
      ·
        exact (plan_call_bound g w hx).trans (by simp only [grade_cons,itemGrade]; omega)
    | inr y =>
      have ht := splitRun_length w
      have hj := splitRun_join w
      simp only [plan,List.mem_cons] at hx
      rcases hx with he | hx
      · cases hh : (splitRun w).1 with
        | nil => simp only [hh] at he; cases he
        | cons z zs =>
          simp only [hh] at he
          cases he
          rw [←hj]
          simp only [grade_cons,itemGrade,grade_append,grade_raws,hh]
          simp only [List.length_append]
          omega
      · have hp := plan_call_bound g (splitRun w).2 hx
        rw [←hj]
        simp only [grade_cons,itemGrade,grade_append]
        omega
termination_by w.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

def Action.partial (f : List S → Part (List S)) : Action C S → Part (Item C S)
  | .keep c => Part.some (.inl c)
  | .raw x => Part.some (.inr x)
  | .call x => (f x).map Sum.inr

def execute (f : List S → Part (List S)) : List (Action C S) → Part (List (Item C S))
  | [] => Part.some []
  | a::w => (a.partial f).bind fun b => (execute f w).map (b::·)

theorem execute_total_mem {f : List S → Part (List S)} {t : List S → List S}
    (p : List (Action C S)) (h : ∀ x, Action.call x ∈ p → t x ∈ f x) :
    p.map (Action.total t) ∈ execute f p := by
  induction p with
  | nil => exact Part.mem_some []
  | cons a p ih =>
    have hp := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha : Action.total t a ∈ Action.partial f a := by
      cases a with
      | keep c => exact Part.mem_some _
      | raw x => exact Part.mem_some _
      | call x => exact (Part.mem_map_iff _).mpr ⟨t x,h x (List.mem_cons_self),rfl⟩
    exact Part.mem_bind_iff.mpr ⟨_,ha,(Part.mem_map_iff _).mpr ⟨_,hp,rfl⟩⟩

def partialSource (f : List S → Part (List S)) (w : List (Item C S)) : Part (List (Item C S)) :=
  execute f (plan w)

theorem partialSource_total_mem (g : C → ℕ) {f : List S → Part (List S)} {t : List S → List S}
    (w : List (Item C S)) (h : ∀ x, x.length ≤ grade g w → t x ∈ f x) :
    source t w ∈ partialSource f w := by
  rw [←plan_total t]
  exact execute_total_mem _ (fun x hx => h x (plan_call_bound g w hx))

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The manuscript's partial normalizer. It is defined even for a divergent
    program; no arbitrary value is inserted for an undefined call. -/
def partialNormal (f : List S → Part (List S)) (w : List (Letter S Γ Q)) : Part (List (Letter S Γ Q)) :=
  if Path.shape w = .zero then Part.some [.zero] else
    (RawRuns.partialSource f ((preprocess A M w).map (classify A.blank))).map
      (List.flatMap (realize A.blank))

/-- Agreement only needs the values below the *input's* additive grade. -/
theorem partialNormal_total_mem {f : List S → Part (List S)} {t : List S → List S}
    (w : List (Letter S Γ Q)) (h : ∀ x, x.length ≤ grade w → t x ∈ f x) :
    normal A M t w ∈ partialNormal A M f w := by
  unfold normal partialNormal
  split
  · exact Part.mem_some _
  · apply (Part.mem_map_iff _).mpr
    refine ⟨_,RawRuns.partialSource_total_mem grade _ ?_,rfl⟩
    intro x hx
    apply h x
    apply hx.trans
    rw [classify_grade]
    exact preprocess_grade A M w

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler

/-- Literal domain/length/context premises of the finite compiler's bounded theorem.
    These are conditions on the given partial program, not a total replacement. -/
structure PartialBudget {S : Type*} (f : List S → Part (List S)) (m : ℕ) : Prop where
  total : ∀ w, w.length ≤ m → (f w).Dom
  length : ∀ w, w.length ≤ m → ∀ out ∈ f w, out.length ≤ w.length
  context : ∀ x w y, (x++w++y).length ≤ m →
    ∀ out ∈ f w, f (x++out++y) = f (x++w++y)

/-- Used only to state the bounded correctness proof of the partial algorithm.
    It has no place in its definition or in its claimed effective implementation. -/
noncomputable def partValue {S : Type*} (p : Part (List S)) : List S := by
  classical
  exact if h : p.Dom then p.get h else []

theorem partValue_mem {S : Type*} {p : Part (List S)} (h : p.Dom) : partValue p ∈ p := by
  simp only [partValue,dite_eq_left h]
  exact Part.get_mem h

theorem partValue_eq {S : Type*} {p : Part (List S)} {x : List S} (h : x ∈ p) : partValue p = x :=
  Part.mem_unique (partValue_mem h.1) h

theorem PartialBudget.totalize {S : Type*} {f : List S → Part (List S)} {m : ℕ}
    (h : PartialBudget f m) : RawRuns.Budget (fun w => partValue (f w)) m where
  length w hw := h.length w hw _ (partValue_mem (h.total w hw))
  context x w y hw := by
    have hh : w.length ≤ m := by simp only [List.length_append] at hw; omega
    exact congrArg partValue (h.context x w y hw _ (partValue_mem (h.total w hh)))

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The finite-machine adapter has to *prove* this execution specification for
    any supplied partial-recursive program. It is not an extra main hypothesis. -/
def Realizes (f : List S → Part (List S)) : Prop :=
  ∀ w out, out ∈ f w ↔ ∃ c,
    ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M w) c ∧
    Simulator.Halted A M c ∧ Simulator.Returns A c out

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem Realizes.computesAt {f : List S → Part (List S)} (hr : Realizes A M f) {m : ℕ}
    (h : PartialBudget f m) : ComputesAt A M (fun w => partValue (f w)) m := by
  intro w hw
  exact (hr w _).mp (partValue_mem (h.total w hw))

theorem partialNormal_eq_some {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m)
    (w : List (Letter S Γ Q)) (hw : grade w ≤ m) :
    partialNormal A M f w = Part.some (normal A M (fun x => partValue (f x)) w) := by
  apply Part.eq_some_iff.mpr
  exact partialNormal_total_mem A M w (fun x hx => partValue_mem (h.total x (hx.trans hw)))

theorem partialNormal_terminates {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m)
    (w : List (Letter S Γ Q)) (hw : grade w ≤ m) : (partialNormal A M f w).Dom := by
  rw [partialNormal_eq_some A M h w hw]
  trivial

theorem partialNormal_reduces {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m)
    (hr : Realizes A M f) (w : List (Letter S Γ Q)) (hw : grade w ≤ m)
    {out : List (Letter S Γ Q)} (ho : out ∈ partialNormal A M f w) :
    Reduces A M w out := by
  rw [partialNormal_eq_some A M h w hw,Part.mem_some_iff] at ho
  subst out
  exact reduces_normal A M h.totalize (Realizes.computesAt A M hr h) w hw

theorem partialNormal_rule
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m) (hr : Realizes A M f)
    {u v : List (Letter S Γ Q)} (he : Rule A M u v) (x y : List (Letter S Γ Q))
    (hu : grade (x++u++y) ≤ m) (hv : grade (x++v++y) ≤ m) :
    partialNormal A M f (x++u++y) = partialNormal A M f (x++v++y) := by
  rw [partialNormal_eq_some A M h _ hu,partialNormal_eq_some A M h _ hv,
    normal_rule A M hdecode h.totalize (Realizes.computesAt A M hr h) he x y hu hv]

theorem partialNormal_context
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m) (hr : Realizes A M f)
    {u v : List (Letter S Γ Q)} (he : partialNormal A M f u = partialNormal A M f v)
    (x y : List (Letter S Γ Q))
    (hu : grade (x++u++y) ≤ m) (hv : grade (x++v++y) ≤ m) :
    partialNormal A M f (x++u++y) = partialNormal A M f (x++v++y) := by
  have hu' : grade u ≤ m := by simp only [grade_append] at hu; omega
  have hv' : grade v ≤ m := by simp only [grade_append] at hv; omega
  rw [partialNormal_eq_some A M h u hu',partialNormal_eq_some A M h v hv'] at he
  have hn : normal A M (fun w => partValue (f w)) u = normal A M (fun w => partValue (f w)) v := by
    exact Part.some_inj.mp he
  rw [partialNormal_eq_some A M h _ hu,partialNormal_eq_some A M h _ hv,
    normal_context A M hdecode h.totalize (Realizes.computesAt A M hr h) hn x y hu hv]

end FiniteAlgebraicEnvelopes.Compiler.Word

end OAI
