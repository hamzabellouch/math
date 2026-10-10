import OAI.Computability.FiniteCompiler.Simulator

namespace OAI

/-!
Finite control and bounded compiler orbit normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Cleanup
open Relation
variable {S Γ : Type*}

inductive Head
  | cleanup | raw
  deriving DecidableEq

instance : Fintype Head := ⟨{.cleanup,.raw}, by intro h; cases h <;> simp⟩

abbrev Sector (S Γ : Type*) := Scan.Sector Head (Base S) (Tag S Γ)

/-- Exactly the cleanup letter prescribed in the finite compiler. Output marks
    on nonanchors are deliberately ignored even on dirty configurations. -/
def emit (c : Base S × Tag S Γ) : Option S :=
  match c.1 with
  | .anchor _ => c.2.output
  | _ => none

def letter (blank : Γ) (a : S) : Base S × Tag S Γ := (.anchor a,clean blank)

def output (blank : Γ) (l : List (Base S × Tag S Γ)) : List (Base S × Tag S Γ) :=
  (l.filterMap emit).map (letter blank)

/-- The left sweep deletes every consumed tagged cell, and only marks on
    anchors produce a clean right-hand anchor. The boundary test is literal. -/
def step (blank : Γ) (v : Sector S Γ) : Option (Sector S Γ) :=
  match v.head with
  | .raw => none
  | .cleanup => match v.left with
    | c::l => some { v with left := l, right := (emit c).toList.map (letter blank) ++ v.right }
    | [] => if v.leftBoundary then some {v with head := .raw} else none

def Step (blank : Γ) (v w : Sector S Γ) : Prop := step blank v = some w

theorem deterministic (blank : Γ) : Relator.RightUnique (Step (S := S) blank) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

@[simp] theorem output_nil (blank : Γ) : output (S := S) blank [] = [] := rfl

@[simp] theorem output_append (blank : Γ) (l r : List (Base S × Tag S Γ)) :
    output blank (l++r) = output blank l ++ output blank r := by
  simp [output,List.filterMap_append]

@[simp] theorem output_singleton (blank : Γ) (c : Base S × Tag S Γ) :
    output blank [c] = (emit c).toList.map (letter blank) := by
  cases h : emit c <;> simp [output,h]

/-- Each consumed cell is emitted before all previously emitted cells. This
    proves the leftward cleanup's order on arbitrary—not only clean—data. -/
theorem sweep (blank : Γ) (l r : List (Base S × Tag S Γ)) (a b : Bool) :
    ReflTransGen (Step blank) ⟨l,.cleanup,r,a,b⟩
      ⟨[],.cleanup,output blank l.reverse ++ r,a,b⟩ := by
  induction l generalizing r with
  | nil => exact .refl
  | cons c l ih =>
      have h : Step blank ⟨c::l,.cleanup,r,a,b⟩
          ⟨l,.cleanup,(emit c).toList.map (letter blank) ++ r,a,b⟩ := rfl
      simpa [List.reverse_cons,List.append_assoc] using
        (ReflTransGen.single h).trans (ih ((emit c).toList.map (letter blank) ++ r))

/-- Normalization of a cleanup head, with or without a left boundary. -/
def normal (blank : Γ) (v : Sector S Γ) : Sector S Γ :=
  match v.head with
  | .raw => v
  | .cleanup => ⟨[],if v.leftBoundary then .raw else .cleanup,
      output blank v.left.reverse ++ v.right,v.leftBoundary,v.rightBoundary⟩

theorem normal_reached (blank : Γ) (v : Sector S Γ) :
    ReflTransGen (Step blank) v (normal blank v) := by
  rcases v with ⟨l,h,r,a,b⟩
  cases h with
  | raw => exact .refl
  | cleanup =>
      have hr := sweep blank l r a b
      cases a with
      | false => exact hr
      | true => exact hr.tail rfl

theorem normal_terminal (blank : Γ) (v : Sector S Γ) :
    step blank (normal blank v) = none := by
  rcases v with ⟨l,h,r,a,b⟩
  cases h <;> cases a <;> rfl

/-- Cleanup normal forms are invariant under either direction of any local
    cleanup equation, including in dirty sectors with missing boundaries. -/
theorem normal_invariant (blank : Γ) {v w : Sector S Γ}
    (h : EqvGen (Step blank) v w) : normal blank v = normal blank w := by
  have tv : ∀ z, ¬Step blank (normal blank v) z := by
    intro z hz
    change step blank (normal blank v) = some z at hz
    rw [normal_terminal] at hz
    cases hz
  have tw : ∀ z, ¬Step blank (normal blank w) z := by
    intro z hz
    change step blank (normal blank w) = some z at hz
    rw [normal_terminal] at hz
    cases hz
  apply terminal_unique (deterministic blank) tv tw
  exact EqvGen.trans _ _ _
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (normal_reached blank v)))
    (EqvGen.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (normal_reached blank w)))

/-- Cleanup forgets empty marks, not anchor order. -/
theorem emit_anchorView (l : List (Base S × Tag S Γ)) :
    l.filterMap emit = (Simulator.anchorView l).filterMap id := by
  rw [Simulator.anchorView,List.filterMap_filterMap]
  congr 1
  funext c
  rcases c with ⟨b,t⟩
  cases b <;> rfl

theorem emit_returned (l : List (Base S × Tag S Γ)) (out : List S) (n : ℕ)
    (h : Simulator.anchorView l = out.map some ++ List.replicate n none) :
    l.filterMap emit = out := by
  rw [emit_anchorView,h,List.filterMap_append]
  simp

/-- Exact successful cleanup, including empty returned strings. -/
theorem success (blank : Γ) (l : List (Base S × Tag S Γ)) (out : List S) (n : ℕ)
    (h : Simulator.anchorView l = out.map some ++ List.replicate n none) :
    ReflTransGen (Step blank) ⟨l.reverse,.cleanup,[],true,true⟩
      ⟨[],.raw,out.map (letter blank),true,true⟩ := by
  have hr := normal_reached blank (⟨l.reverse,.cleanup,[],true,true⟩ : Sector S Γ)
  simpa [normal,output,emit_returned l out n h] using hr

def grade : Base S → ℕ
  | .cutC => 2
  | .workspace => 0
  | _ => 1

def cellsGrade (l : List (Base S × Tag S Γ)) : ℕ := (l.map (grade ∘ Prod.fst)).sum

@[simp] theorem cellsGrade_append (l r : List (Base S × Tag S Γ)) :
    cellsGrade (l++r) = cellsGrade l + cellsGrade r := by simp [cellsGrade]

@[simp] theorem cellsGrade_reverse (l : List (Base S × Tag S Γ)) :
    cellsGrade l.reverse = cellsGrade l := by simp [cellsGrade,List.map_reverse]

/-- Grade is nonincreasing for EVERY tagged cleanup cell. Workspace marks do
    not emit letters, so grade-zero workspace can never create positive grade. -/
theorem output_grade_le (blank : Γ) (l : List (Base S × Tag S Γ)) :
    cellsGrade (output blank l) ≤ cellsGrade l := by
  induction l with
  | nil => simp [cellsGrade]
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b <;> simp only [output,List.filterMap_cons,emit]
      · cases t.output <;> simp_all [output,cellsGrade,letter,grade]
        omega
      all_goals simp_all [output,cellsGrade,grade]
      all_goals omega

end FiniteAlgebraicEnvelopes.Compiler.Cleanup

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*}

/-- An explicit bounded list enumeration, used only for finite internal search.
    This bound counts cells, not grade, and thus never admits quota insertion. -/
def boundedLists (α : Type*) [Fintype α] [DecidableEq α] : ℕ → Finset (List α)
  | 0 => {[]}
  | n+1 => {[]} ∪ ((Finset.univ : Finset α) ×ˢ boundedLists α n).image (fun p => p.1::p.2)

@[simp] theorem mem_boundedLists (α : Type*) [Fintype α] [DecidableEq α]
    (n : ℕ) (l : List α) : l ∈ boundedLists α n ↔ l.length ≤ n := by
  induction n generalizing l with
  | zero => simp [boundedLists]
  | succ n ih =>
      cases l with
      | nil => simp [boundedLists]
      | cons a l => simp [boundedLists,ih]

variable [Fintype H] [Fintype B] [Fintype T]
variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

/-- The finite search universe consists of actual list-zipper sectors. -/
def boundedSectors (k : ℕ) : Finset (Sector H B T) :=
  (((((Finset.univ : Finset H) ×ˢ boundedLists (B×T) k) ×ˢ boundedLists (B×T) k) ×ˢ
      (Finset.univ : Finset Bool)) ×ˢ (Finset.univ : Finset Bool)).image
    (fun p => ⟨p.1.1.1.2,p.1.1.1.1,p.1.1.2,p.1.2,p.2⟩)

@[simp] theorem mem_boundedSectors (k : ℕ) (v : Sector H B T) :
    v ∈ boundedSectors k ↔ v.left.length ≤ k ∧ v.right.length ≤ k := by
  rcases v with ⟨l,q,r,a,b⟩
  simp [boundedSectors,Sector.mk.injEq]

/-- Filtering by bases and boundary flags gives exactly the source's fixed
    internal-search state space. This is computable from the literal sector. -/
def searchUniverse (v : Sector H B T) : Finset (Sector H B T) :=
  (boundedSectors (v.left.length+v.right.length)).filter
    (fun w => baseSkeleton w = baseSkeleton v)

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
theorem skeleton_length {v w : Sector H B T} (h : baseSkeleton v = baseSkeleton w) :
    v.left.length+v.right.length = w.left.length+w.right.length := by
  have hl := congrArg (fun p : List B × Bool × Bool => p.1.length) h
  simpa [baseSkeleton] using hl

@[simp] theorem mem_universe (v w : Sector H B T) :
    w ∈ searchUniverse v ↔ baseSkeleton w = baseSkeleton v := by
  simp only [searchUniverse,Finset.mem_filter,mem_boundedSectors,and_iff_right_iff_imp]
  intro h
  have hl := skeleton_length h
  constructor <;> omega

abbrev Fixed (v : Sector H B T) := {w : Sector H B T // baseSkeleton w = baseSkeleton v}

instance fixedFintype (v : Sector H B T) : Fintype (Fixed v) :=
  Fintype.subtype (searchUniverse v) (mem_universe v)

def fixedSelf (v : Sector H B T) : Fixed v := ⟨v,rfl⟩

def fixedStep (table : Table H B T) (v : Sector H B T) (a b : Fixed v) : Prop :=
  Step table a.val b.val

instance fixedStepDecidable (table : Table H B T) (v : Sector H B T) :
    DecidableRel (fixedStep table v) := fun _ _ => inferInstanceAs (Decidable (_ = _))

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
theorem connected_skeleton (table : Table H B T) {x y : Sector H B T}
    (h : EqvGen (Step table) x y) : baseSkeleton x = baseSkeleton y := by
  induction h with
  | rel _ _ h => exact step_skeleton table h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
/-- A weak path with fixed baselines lifts to the finite search universe. -/
theorem fixedConnected_iff (table : Table H B T) (v : Sector H B T) (a b : Fixed v) :
    EqvGen (fixedStep table v) a b ↔ EqvGen (Step table) a.val b.val := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact .rel _ _ h
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro h
    have lift : ∀ x y, EqvGen (Step table) x y →
        ∀ (hx : baseSkeleton x = baseSkeleton v),
        ∃ (hy : baseSkeleton y = baseSkeleton v),
          EqvGen (fixedStep table v) ⟨x,hx⟩ ⟨y,hy⟩ := by
      intro x y h
      induction h with
      | rel x y h =>
          intro hx
          exact ⟨(step_skeleton table h).symm.trans hx,.rel _ _ h⟩
      | refl x => intro hx; exact ⟨hx,.refl _⟩
      | symm x y h ih =>
          intro hy
          have hbase := connected_skeleton table h
          obtain ⟨_,hr⟩ := ih (hbase.trans hy)
          exact ⟨hbase.trans hy,.symm _ _ hr⟩
      | trans x y z _ _ ih₁ ih₂ =>
          intro hx
          obtain ⟨hy,hxy⟩ := ih₁ hx
          obtain ⟨hz,hyz⟩ := ih₂ hy
          exact ⟨hz,.trans _ _ _ hxy hyz⟩
    obtain ⟨_,h'⟩ := lift a.val b.val h a.property
    exact h'

/-- Operational component equality has a finite decision procedure. Its only
    primitives are the finite table, tagged cells, and bounded finite search. -/
def connectedDecision (table : Table H B T) (v : Sector H B T) (w : Fixed v) : Bool :=
  decideConnected (fixedStep table v) (fixedSelf v) w

@[simp] theorem connectedDecision_eq_true (table : Table H B T)
    (v : Sector H B T) (w : Fixed v) :
    connectedDecision table v w = true ↔ EqvGen (Step table) v w.val := by
  rw [connectedDecision,decideConnected_eq_true,fixedConnected_iff]
  rfl

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Compiled

section
open Relation
variable {S Γ Q : Type*}
abbrev MachineSector (S Γ Q : Type*) := Scan.Sector (Simulator.Head S Q) (Base S) (Tag S Γ)
abbrev Cfg (S Γ Q : Type*) := Validator.Extended.Cfg S Γ (MachineSector S Γ Q)

/-- The fresh handoff is one state, not two copies joined by an artificial edge. -/
def embed (v : MachineSector S Γ Q) : Cfg S Γ Q :=
  match v.head with
  | .start => .inl ⟨.start,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | _ => .inr v

def project : Cfg S Γ Q → MachineSector S Γ Q
  | .inl v => ⟨v.left,.start,v.right,v.leftBoundary,v.rightBoundary⟩
  | .inr v => v

@[simp] theorem project_embed (v : MachineSector S Γ Q) : project (embed v) = v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> rfl

theorem embed_injective : Function.Injective (@embed S Γ Q) := by
  intro a b h
  simpa only [project_embed] using congrArg project h

@[simp] theorem embed_active (v : MachineSector S Γ Q) : Validator.Extended.Active (embed v) := by
  unfold embed
  split <;> trivial

@[simp] theorem embed_project {v : Cfg S Γ Q} (hv : Validator.Extended.Active v)
    (hc : ∀ u, v = .inr u → u.head ≠ .start) : embed (project v) = v := by
  cases v with
  | inl v => simp only [Validator.Extended.Active] at hv; cases v; cases hv; rfl
  | inr v =>
      have h := hc v rfl
      simp only [project,embed]

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) [DecidableEq Γ]

def MachineRel (a b : Cfg S Γ Q) : Prop :=
  ∃ u v, a = embed u ∧ b = embed v ∧ Scan.Step (Simulator.table A M) u v

def Step : Cfg S Γ Q → Cfg S Γ Q → Prop :=
  Validator.Extended.Step A.blank (MachineRel A M)

theorem machine_deterministic : Relator.RightUnique (MachineRel A M) := by
  rintro a b c ⟨u,v,rfl,rfl,h⟩ ⟨u',v',he,rfl,h'⟩
  cases embed_injective he
  exact congrArg embed (Scan.deterministic _ h h')

theorem deterministic : Relator.RightUnique (Step A M) :=
  Validator.Extended.deterministic A.blank (machine_deterministic A M)

abbrev bases : Cfg S Γ Q → List (Base S) × Bool × Bool :=
  Validator.Extended.baseSkeleton Scan.baseSkeleton

omit [DecidableEq Γ] in
@[simp] theorem embed_bases (v : MachineSector S Γ Q) : bases (embed v) = Scan.baseSkeleton v := by
  unfold embed
  split <;> rfl

theorem machine_bases (a b : Cfg S Γ Q) (h : MachineRel A M a b) : bases a = bases b := by
  obtain ⟨u,v,rfl,rfl,h⟩ := h
  simpa only [embed_bases] using Scan.step_skeleton _ h

/-- The manuscript's uniqueness of entries, now for the concrete copy/run/read
    table, not for an unspecified simulated relation. -/
theorem entries_unique {a b : Validator.Sector S Γ}
    (ha : Validator.Entry A.blank a) (hb : Validator.Entry A.blank b)
    (h : EqvGen (Step A M) (.inl a) (.inl b)) : a = b :=
  Validator.Extended.entries_unique A.blank Scan.baseSkeleton
    (machine_deterministic A M) (machine_bases A M) ha hb h

theorem embed_step {u v : MachineSector S Γ Q}
    (h : Scan.Step (Simulator.table A M) u v) : Step A M (embed u) (embed v) :=
  .machine (embed_active u) (embed_active v) ⟨u,v,rfl,rfl,h⟩

theorem embed_run {u v : MachineSector S Γ Q}
    (h : ReflTransGen (Scan.Step (Simulator.table A M)) u v) :
    ReflTransGen (Step A M) (embed u) (embed v) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (embed_step A M hs)

theorem validator_run {u v : Validator.Sector S Γ}
    (h : ReflTransGen (Validator.Step A.blank) u v) :
    ReflTransGen (Step A M) (.inl u) (.inl v) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.validator hs)

theorem active_step {a b : Cfg S Γ Q} (ha : Validator.Extended.Active a)
    (h : Step A M a b) : MachineRel A M a b := by
  cases h with
  | validator h => exact False.elim (Validator.Extended.validator_not_start A.blank h ha)
  | machine _ _ h => exact h

/-- A path retains its actual simulator suffix after the unique validation
    handoff. This rules out a dirty intermediate state being treated as input. -/
theorem path_decomposition {a : Validator.Sector S Γ} {b : Cfg S Γ Q}
    (h : ReflTransGen (Step A M) (.inl a) b) :
    (∃ v, b = .inl v ∧ ReflTransGen (Validator.Step A.blank) a v) ∨
    ∃ v u, ReflTransGen (Validator.Step A.blank) a v ∧ v.head = .start ∧
      b = embed u ∧ ReflTransGen (Scan.Step (Simulator.table A M)) (project (.inl v)) u := by
  induction h with
  | refl => exact Or.inl ⟨a,rfl,.refl⟩
  | @tail b c _ hs ih =>
      rcases ih with ⟨v,rfl,hv⟩ | ⟨v,u,hv,hq,rfl,hr⟩
      · cases hs with
        | validator hs => exact Or.inl ⟨_,rfl,hv.tail hs⟩
        | machine ha _ hs =>
            obtain ⟨u,w,hu,rfl,hw⟩ := hs
            have he : project (.inl v) = u := by rw [hu,project_embed]
            exact Or.inr ⟨v,w,hv,ha,rfl,by rw [he]; exact .single hw⟩
      · obtain ⟨u',w,he,rfl,hw⟩ := active_step A M (embed_active u) hs
        cases embed_injective he
        exact Or.inr ⟨v,w,hv,hq,rfl,hr.tail hw⟩

theorem ok_terminal {v : MachineSector S Γ Q} (hv : v.head = .ok) :
    Terminal (Step A M) (embed v) := by
  intro u h
  have he : embed v = .inr v := by simp [embed,hv]
  rw [he] at h
  cases h with
  | machine _ _ h =>
      obtain ⟨v',w,hv',_,h⟩ := h
      have hsame : v = v' := embed_injective (he.trans hv')
      subst v'
      rw [Scan.Step,Simulator.ok_terminal A M v hv] at h
      contradiction

/-- Arbitrary dirty accepting sectors are unique within a weak component. -/
theorem ok_unique {u v : MachineSector S Γ Q} (hu : u.head = .ok) (hv : v.head = .ok)
    (h : EqvGen (Step A M) (embed u) (embed v)) : u = v :=
  embed_injective (terminal_unique (deterministic A M) (ok_terminal A M hu) (ok_terminal A M hv) h)

end

open Relation
variable {S Γ Q : Type*}

/-- The literal entry and handoff of compiler-clean-entry. -/
def cleanEntry (blank : Γ) (x y : List S) (s : ℕ) : Validator.Sector S Γ :=
  ⟨.initial,List.replicate s (Validator.cell blank .workspace) ++
    Validator.cell blank .cutC :: (x.map (fun a => Validator.cell blank (.anchor a))).reverse,
    Validator.cell blank .cutD :: y.map (fun a => Validator.cell blank (.anchor a)),true,true⟩

def handoff (blank : Γ) (x y : List S) (s : ℕ) : Validator.Sector S Γ :=
  ⟨.start,(y.map (fun a => Validator.cell blank (.anchor a))).reverse ++
    Validator.cell blank .cutD :: (List.replicate s (Validator.cell blank .workspace) ++
    Validator.cell blank .cutC :: (x.map (fun a => Validator.cell blank (.anchor a))).reverse),
    [],true,true⟩

@[simp] theorem cleanEntry_entry (blank : Γ) (x y : List S) (s : ℕ) :
    Validator.Entry blank (cleanEntry blank x y s) := ⟨rfl,_,rfl⟩

theorem cleanEntry_reaches (blank : Γ) (x y : List S) (s : ℕ) :
    ReflTransGen (Validator.Step blank) (cleanEntry blank x y s) (handoff blank x y s) :=
  Validator.clean_entry_reaches blank x y s

theorem validator_start_terminal (blank : Γ) {v : Validator.Sector S Γ}
    (hv : v.head = .start) : Terminal (Validator.Step blank) v := by
  intro w h
  exact Validator.Extended.validator_not_start blank h hv

theorem handoff_unique (blank : Γ) (x y : List S) (s : ℕ) {v : Validator.Sector S Γ}
    (h : ReflTransGen (Validator.Step blank) (cleanEntry blank x y s) v)
    (hv : v.head = .start) : v = handoff blank x y s := by
  apply terminal_unique (Validator.step_deterministic blank)
    (validator_start_terminal blank hv) (validator_start_terminal blank rfl)
  exact EqvGen.trans _ _ _
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ h))
    (EqvGen.reflTransGen_le_eqvGen _ _ _ (cleanEntry_reaches blank x y s))

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) [DecidableEq Γ]

omit [DecidableEq Γ] in
@[simp] theorem project_handoff (x y : List S) (s : ℕ) :
    (project (.inl (handoff A.blank x y s)) : MachineSector S Γ Q) =
      ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ := by
  simp [project,handoff,Simulator.body,Simulator.readAnchor,Simulator.bare,Validator.cell,
    clean,List.append_assoc]

/-- Clean entries that meet an accepting internal sector really passed the
    validator and then ran this very machine. No cleanliness is assumed of the
    sector used for finding its weak component. -/
theorem accepting_entry_runs {a : Validator.Sector S Γ} {b : MachineSector S Γ Q}
    (ha : Validator.Entry A.blank a) (hb : b.head = .ok)
    (h : EqvGen (Step A M) (.inl a) (embed b)) :
    ∃ x y s, a = cleanEntry A.blank x y s ∧
      ReflTransGen (Scan.Step (Simulator.table A M))
        ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ b := by
  have hr := reaches_terminal (deterministic A M) (ok_terminal A M hb) h
  rcases path_decomposition A M hr with ⟨v,hv,_⟩ | ⟨v,u,hv,hq,hu,hr⟩
  · simp [embed,hb] at hv
  · have hub : b = u := embed_injective hu
    subst u
    obtain ⟨x,y,s,he⟩ := Validator.passing_entry A.blank ha hv hq
    change a = cleanEntry A.blank x y s at he
    subst a
    have he := handoff_unique A.blank x y s hv hq
    subst v
    exact ⟨x,y,s,rfl,by simpa only [project_handoff] using hr⟩

/-- Concrete soundness part of Lemma compiler-components: true halted output,
    the exact length bound, AND the mandated literal cleanup word. Quota
    insufficiency is ruled out by the previously proved rejection theorem. -/
theorem accepting_entry_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {a : Validator.Sector S Γ} {b : MachineSector S Γ Q}
    (ha : Validator.Entry A.blank a) (hb : b.head = .ok)
    (h : EqvGen (Step A M) (.inl a) (embed b)) :
    ∃ x y s n c out, ∃ (result : List (Base S × Tag S Γ)),
      a = cleanEntry A.blank x y s ∧ s = x.length+y.length+n+1 ∧
      ReflTransGen (Simulator.TapeStep M)
        (Simulator.pad A (Simulator.initialTape A M (x++y)) (n+1)) c ∧
      Simulator.Halted A M c ∧ Simulator.Returns A c out ∧
      out.length ≤ x.length+y.length ∧ b = ⟨result.reverse,.ok,[],true,true⟩ ∧
      ReflTransGen (Cleanup.Step A.blank) ⟨result.reverse,.cleanup,[],true,true⟩
        ⟨[],.raw,out.map (Cleanup.letter A.blank),true,true⟩ := by
  obtain ⟨x,y,s,he,hr⟩ := accepting_entry_runs A M ha hb h
  obtain ⟨n,c,out,result,hs,hc,hhalt,hout,hlen,hb,hres⟩ :=
    Simulator.simulation_sound A M hdecode x y s hr hb
  exact ⟨x,y,s,n,c,out,result,he,hs,hc,hhalt,hout,hlen,hb,
    Cleanup.success A.blank result out _ hres⟩

/-- Conversely an actual finite halted computation with the required output
    bound has some quota and gives entry-to-ok reachability and exact cleanup. -/
theorem clean_success (x y out : List S)
    (c : Simulator.Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M (x++y)) c)
    (hhalt : Simulator.Halted A M c) (hout : Simulator.Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    ∃ s, ∃ (result : List (Base S × Tag S Γ)), ReflTransGen (Step A M) (.inl (cleanEntry A.blank x y s))
      (embed ⟨result.reverse,.ok,[],true,true⟩) ∧
      ReflTransGen (Cleanup.Step A.blank) ⟨result.reverse,.cleanup,[],true,true⟩
        ⟨[],.raw,out.map (Cleanup.letter A.blank),true,true⟩ := by
  obtain ⟨s,result,hr,hres⟩ := Simulator.simulation_complete A M x y out c hrun hhalt hout hlen
  refine ⟨s,result,?_,Cleanup.success A.blank result out _ hres⟩
  have hv := validator_run A M (cleanEntry_reaches A.blank x y s)
  have he : (.inl (handoff A.blank x y s) : Cfg S Γ Q) =
      embed ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ := by
    rw [← project_handoff]
    rfl
  rw [he] at hv
  exact hv.trans (embed_run A M hr)

end FiniteAlgebraicEnvelopes.Compiler.Compiled

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
variable {S Γ : Type*}

instance : Fintype Head :=
  ⟨{.initial,.left,.right,.workspace,.suffix,.start},by intro h; cases h <;> simp⟩

def toScan (v : Sector S Γ) : Scan.Sector Head (Base S) (Tag S Γ) :=
  ⟨v.left,v.head,v.right,v.leftBoundary,v.rightBoundary⟩

def ofScan (v : Scan.Sector Head (Base S) (Tag S Γ)) : Sector S Γ :=
  ⟨v.head,v.left,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem toScan_ofScan (v : Scan.Sector Head (Base S) (Tag S Γ)) :
    toScan (ofScan v) = v := rfl
@[simp] theorem ofScan_toScan (v : Sector S Γ) : ofScan (toScan v) = v := rfl

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

/-- The displayed validator equations as an executable finite scan table. -/
def table : Table Head (Base S) (Tag S Γ) where
  direction
    | .initial | .left => .left
    | _ => .right
  cell q b t := if t = clean blank then
    match q,b with
    | .initial,.workspace => some ⟨.initial,t,true⟩
    | .initial,.cutC => some ⟨.left,t,true⟩
    | .left,.anchor _ => some ⟨.left,t,true⟩
    | .right,.anchor _ => some ⟨.right,t,true⟩
    | .right,.cutC => some ⟨.workspace,t,true⟩
    | .workspace,.workspace => some ⟨.workspace,t,true⟩
    | .workspace,.cutD => some ⟨.suffix,t,true⟩
    | .suffix,.anchor _ => some ⟨.suffix,t,true⟩
    | _,_ => none
    else none
  boundary
    | .left => some .right
    | .suffix => some .start
    | _ => none

theorem step_toScan {v w : Sector S Γ} (h : Step blank v w) :
    Scan.Step (table blank) (toScan v) (toScan w) := by
  cases h <;> simp [Scan.Step,Scan.step,toScan,table,cell]

theorem step_ofScan {v w : Scan.Sector Head (Base S) (Tag S Γ)}
    (h : Scan.Step (table blank) v w) : Step blank (ofScan v) (ofScan w) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | initial =>
      cases l with
      | nil => cases a <;> simp [Scan.Step,Scan.step,table] at h
      | cons c l =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .initial_cut _ _ _ _ | exact .initial_workspace _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | left =>
      cases l with
      | nil =>
          cases a <;> simp [Scan.Step,Scan.step,table] at h
          subst w; exact .left_boundary _ _
      | cons c l =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            subst w; exact .left_anchor _ _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | right =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .right_anchor _ _ _ _ _ | exact .right_cut _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | workspace =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .workspace _ _ _ _ | exact .workspace_cut _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | suffix =>
      cases r with
      | nil =>
          cases b <;> simp [Scan.Step,Scan.step,table] at h
          subst w; exact .suffix_boundary _ _
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            subst w; exact .suffix_anchor _ _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | start =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank <;> simp [Scan.Step,Scan.step,table,ht] at h

@[simp] theorem step_iff_scan (v w : Sector S Γ) :
    Step blank v w ↔ Scan.Step (table blank) (toScan v) (toScan w) :=
  ⟨step_toScan blank,step_ofScan blank⟩

instance stepDecidable : DecidableRel (Step (S := S) blank) := fun v w => by
  letI : Decidable (Scan.Step (table blank) (toScan v) (toScan w)) :=
    inferInstanceAs (Decidable (_ = _))
  exact decidable_of_iff _ (step_iff_scan blank v w).symm

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H H' B T : Type*}

def mapHead (f : H → H') (v : Sector H B T) : Sector H' B T :=
  ⟨v.left,f v.head,v.right,v.leftBoundary,v.rightBoundary⟩

def mapInstruction (f : H → H') (v : Instruction H T) : Instruction H' T :=
  ⟨f v.head,v.tag,v.cross⟩

@[simp] theorem skeleton_mapHead (f : H → H') (v : Sector H B T) :
    baseSkeleton (mapHead f v) = baseSkeleton v := rfl

theorem mapHead_injective {f : H → H'} (hf : Function.Injective f) :
    Function.Injective (@mapHead H H' B T f) := by
  intro v w h
  cases v; cases w
  simp only [mapHead,Sector.mk.injEq] at h
  rcases h with ⟨rfl,hq,rfl,rfl,rfl⟩
  cases hf hq
  rfl

/-- A literal relabeling of finite control commutes with one scan step. Only
    agreement at the current head is needed, permitting fused control tables. -/
theorem step_mapHead (f : H → H') (t : Table H B T) (t' : Table H' B T)
    (v : Sector H B T)
    (hd : t'.direction (f v.head) = t.direction v.head)
    (hc : ∀ b a, t'.cell (f v.head) b a = (t.cell v.head b a).map (mapInstruction f))
    (hb : t'.boundary (f v.head) = (t.boundary v.head).map f) :
    step t' (mapHead f v) = (step t v).map (mapHead f) := by
  rcases v with ⟨l,q,r,a,b⟩
  simp only [mapHead] at hd hc hb ⊢
  unfold step
  simp only [hd]
  cases hdir : t.direction q <;> dsimp only
  · cases l with
    | nil => cases a <;> simp [hb,mapHead,Option.map_map,Function.comp_def]
    | cons c l =>
        rcases c with ⟨base,tag⟩
        dsimp only
        rw [hc]
        cases hcell : t.cell q base tag with
        | none => rfl
        | some ins => rcases ins with ⟨iq,it,ic⟩; cases ic <;> rfl
  · cases r with
    | nil => cases b <;> simp [hb,mapHead,Option.map_map,Function.comp_def]
    | cons c r =>
        rcases c with ⟨base,tag⟩
        dsimp only
        rw [hc]
        cases hcell : t.cell q base tag with
        | none => rfl
        | some ins => rcases ins with ⟨iq,it,ic⟩; cases ic <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Control

section
open Relation
variable {S Γ Q : Type*}

/-- Finite internal-head alphabet, with a single fresh handoff/start state. -/
inductive Head (S Q : Type*)
  | initial | left | right | workspace | suffix
  | machine : Simulator.Head S Q → Head S Q
  deriving DecidableEq, Fintype

def validatorHead : Validator.Head → Head S Q
  | .initial => .initial
  | .left => .left
  | .right => .right
  | .workspace => .workspace
  | .suffix => .suffix
  | .start => .machine .start

def toValidator : Head S Q → Option Validator.Head
  | .initial => some .initial
  | .left => some .left
  | .right => some .right
  | .workspace => some .workspace
  | .suffix => some .suffix
  | .machine _ => none

abbrev Sector (S Γ Q : Type*) := Scan.Sector (Head S Q) (Base S) (Tag S Γ)

def validator (v : Validator.Sector S Γ) : Sector S Γ Q :=
  Scan.mapHead validatorHead (Validator.toScan v)

def machine (v : Compiled.MachineSector S Γ Q) : Sector S Γ Q :=
  Scan.mapHead Head.machine v

def toCfg (v : Sector S Γ Q) : Compiled.Cfg S Γ Q :=
  match v.head with
  | .initial => .inl ⟨.initial,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .left => .inl ⟨.left,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .right => .inl ⟨.right,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .workspace => .inl ⟨.workspace,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .suffix => .inl ⟨.suffix,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .machine q => Compiled.embed ⟨v.left,q,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem cfg_validator (v : Validator.Sector S Γ) : toCfg (validator (Q := Q) v) = .inl v := by
  cases v with | mk q l r a b => cases q <;> rfl

@[simp] theorem cfg_machine (v : Compiled.MachineSector S Γ Q) :
    toCfg (machine v) = Compiled.embed v := rfl

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

/-- The literal finite union of validation and simulation equations. -/
def table : Table (Head S Q) (Base S) (Tag S Γ) where
  direction q := match toValidator q with
    | some v => (Validator.table (S := S) A.blank).direction v
    | none => match q with
      | .machine v => (Simulator.table A M).direction v
      | _ => .right
  cell q b t := match toValidator q with
    | some v => ((Validator.table (S := S) A.blank).cell v b t).map (Scan.mapInstruction validatorHead)
    | none => match q with
      | .machine v => ((Simulator.table A M).cell v b t).map (Scan.mapInstruction Head.machine)
      | _ => none
  boundary q := match toValidator q with
    | some v => ((Validator.table (S := S) A.blank).boundary v).map validatorHead
    | none => match q with
      | .machine v => ((Simulator.table A M).boundary v).map Head.machine
      | _ => none

theorem step_machine (v : Compiled.MachineSector S Γ Q) :
    Scan.step (table A M) (machine v) = (Scan.step (Simulator.table A M) v).map machine := by
  apply Scan.step_mapHead
  · rfl
  · intro b a; rfl
  · rfl

theorem step_validator (v : Validator.Sector S Γ) (hv : v.head ≠ .start) :
    Scan.step (table A M) (validator v) =
      (Scan.step (Validator.table (S := S) A.blank) (Validator.toScan v)).map (Scan.mapHead validatorHead) := by
  apply Scan.step_mapHead
  · cases v with | mk q l r a b => cases q <;> rfl
  · intro b a
    cases v with | mk q l r ls rs => cases q <;> first | rfl | exact False.elim (hv rfl)
  · cases v with | mk q l r a b => cases q <;> first | rfl | exact False.elim (hv rfl)

end

open Relation
variable {S Γ Q : Type*}

def ofCfg : Compiled.Cfg S Γ Q → Sector S Γ Q
  | .inl v => validator v
  | .inr v => machine v

@[simp] theorem ofCfg_embed (v : Compiled.MachineSector S Γ Q) :
    ofCfg (Compiled.embed v) = machine v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> rfl

@[simp] theorem ofCfg_toCfg (v : Sector S Γ Q) : ofCfg (toCfg v) = v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> first | rfl | exact ofCfg_embed _

theorem cfg_injective : Function.Injective (@toCfg S Γ Q) :=
  Function.LeftInverse.injective ofCfg_toCfg

theorem sector_cases (v : Sector S Γ Q) :
    (∃ w : Validator.Sector S Γ, w.head ≠ .start ∧ v = validator w) ∨
    ∃ w : Compiled.MachineSector S Γ Q, v = machine w := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | machine q => exact Or.inr ⟨⟨l,q,r,a,b⟩,rfl⟩
  | initial => exact Or.inl ⟨⟨.initial,l,r,a,b⟩,by simp,rfl⟩
  | left => exact Or.inl ⟨⟨.left,l,r,a,b⟩,by simp,rfl⟩
  | right => exact Or.inl ⟨⟨.right,l,r,a,b⟩,by simp,rfl⟩
  | workspace => exact Or.inl ⟨⟨.workspace,l,r,a,b⟩,by simp,rfl⟩
  | suffix => exact Or.inl ⟨⟨.suffix,l,r,a,b⟩,by simp,rfl⟩

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem validator_step {v w : Validator.Sector S Γ} (h : Validator.Step A.blank v w) :
    Scan.Step (table A M) (validator v) (validator w) := by
  rw [Scan.Step,step_validator A M v (Validator.Extended.validator_not_start A.blank h),
    Validator.step_toScan A.blank h]
  rfl

theorem machine_step {v w : Compiled.MachineSector S Γ Q}
    (h : Scan.Step (Simulator.table A M) v w) :
    Scan.Step (table A M) (machine v) (machine w) := by
  rw [Scan.Step,step_machine A M,h]
  rfl

theorem cfg_step {v w : Sector S Γ Q} (h : Scan.Step (table A M) v w) :
    Compiled.Step A M (toCfg v) (toCfg w) := by
  rcases sector_cases v with ⟨v,hv,rfl⟩ | ⟨v,rfl⟩
  · rw [Scan.Step,step_validator A M v hv] at h
    obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp h
    have he : Scan.mapHead (validatorHead (S := S) (Q := Q)) u =
        validator (Validator.ofScan u) := rfl
    rw [he,cfg_validator,cfg_validator]
    exact .validator (Validator.step_ofScan A.blank hu)
  · rw [Scan.Step,step_machine A M] at h
    obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp h
    rw [cfg_machine,cfg_machine]
    exact Compiled.embed_step A M hu

theorem ofCfg_step {v w : Compiled.Cfg S Γ Q} (h : Compiled.Step A M v w) :
    Scan.Step (table A M) (ofCfg v) (ofCfg w) := by
  cases h with
  | validator h => exact validator_step A M h
  | machine _ _ h =>
      obtain ⟨u,v,rfl,rfl,h⟩ := h
      rw [ofCfg_embed,ofCfg_embed]
      exact machine_step A M h

theorem cfg_connected {v w : Sector S Γ Q} (h : EqvGen (Scan.Step (table A M)) v w) :
    EqvGen (Compiled.Step A M) (toCfg v) (toCfg w) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (cfg_step A M h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem ofCfg_runs {v w : Compiled.Cfg S Γ Q} (h : ReflTransGen (Compiled.Step A M) v w) :
    ReflTransGen (Scan.Step (table A M)) (ofCfg v) (ofCfg w) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (ofCfg_step A M h)

end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*} [Fintype H] [Fintype B] [Fintype T]
  [DecidableEq H] [DecidableEq B] [DecidableEq T]

/-- Literal configurations, rather than an oracle for connectivity, returned
    by exhaustive search on the fixed finite base skeleton. -/
def literalComponent (table : Table H B T) (v : Sector H B T) : Finset (Sector H B T) :=
  (component (fixedStep table v) (fixedSelf v)).image Subtype.val

@[simp] theorem mem_literalComponent (table : Table H B T) (v w : Sector H B T) :
    w ∈ literalComponent table v ↔ EqvGen (Step table) v w := by
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
    exact (fixedConnected_iff table v _ _).mp ((mem_component_iff _ _ _).mp hu)
  · intro h
    let u : Fixed v := ⟨w,(connected_skeleton table h).symm⟩
    apply Finset.mem_image.mpr
    refine ⟨u,?_,rfl⟩
    exact (mem_component_iff _ _ _).mpr ((fixedConnected_iff table v _ _).mpr h)

theorem literalComponent_nonempty (table : Table H B T) (v : Sector H B T) :
    (literalComponent table v).Nonempty :=
  ⟨v,(mem_literalComponent table v v).mpr (.refl v)⟩

theorem literalComponent_eq (table : Table H B T) {v w : Sector H B T}
    (h : EqvGen (Step table) v w) : literalComponent table v = literalComponent table w := by
  ext u
  simp only [mem_literalComponent]
  exact ⟨fun hv => .trans _ _ _ (.symm _ _ h) hv,fun hw => .trans _ _ _ h hw⟩

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
variable {α : Type*}

/-- The priority order in source compiler-normalization: entry first, success
    second, and arbitrary component member only when neither is present. -/
def prioritySet (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (s : Finset α) : Finset α :=
  if (s.filter P).Nonempty then s.filter P
  else if (s.filter Q).Nonempty then s.filter Q else s

theorem prioritySet_subset (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (s : Finset α) :
    prioritySet P Q s ⊆ s := by
  unfold prioritySet
  split <;> first | exact Finset.filter_subset _ _ | skip
  split
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.refl _

theorem prioritySet_nonempty (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (s : Finset α) (hs : s.Nonempty) : (prioritySet P Q s).Nonempty := by
  unfold prioritySet
  split
  · assumption
  · split <;> assumption

theorem prioritySet_first (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    {s : Finset α} (hs : ∃ a ∈ s, P a) {b : α} (hb : b ∈ prioritySet P Q s) : P b := by
  have hn : (s.filter P).Nonempty := by
    obtain ⟨a,ha,hp⟩ := hs
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩⟩
  rw [prioritySet,ite_eq_left hn] at hb
  exact (Finset.mem_filter.mp hb).2

theorem prioritySet_second (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    {s : Finset α} (hp : ¬ ∃ a ∈ s, P a) (hq : ∃ a ∈ s, Q a)
    {b : α} (hb : b ∈ prioritySet P Q s) : Q b := by
  have hn : ¬ (s.filter P).Nonempty := by
    rintro ⟨a,ha⟩
    exact hp ⟨a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2⟩
  have hm : (s.filter Q).Nonempty := by
    obtain ⟨a,ha,hq⟩ := hq
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hq⟩⟩
  rw [prioritySet,ite_eq_right hn,ite_eq_left hm] at hb
  exact (Finset.mem_filter.mp hb).2

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*} [Fintype H] [Fintype B] [Fintype T]
  [DecidableEq H] [DecidableEq B] [DecidableEq T] [LinearOrder (Sector H B T)]
variable (table : Table H B T) (P Q : Sector H B T → Prop) [DecidablePred P] [DecidablePred Q]

def representative (v : Sector H B T) : Sector H B T :=
  (prioritySet P Q (literalComponent table v)).min'
    (prioritySet_nonempty P Q _ (literalComponent_nonempty table v))

theorem representative_mem (v : Sector H B T) :
    representative table P Q v ∈ prioritySet P Q (literalComponent table v) :=
  Finset.min'_mem _ _

theorem representative_connected (v : Sector H B T) :
    EqvGen (Step table) v (representative table P Q v) :=
  (mem_literalComponent table _ _).mp
    (prioritySet_subset _ _ _ (representative_mem table P Q v))

theorem representative_eq {v w : Sector H B T} (h : EqvGen (Step table) v w) :
    representative table P Q v = representative table P Q w := by
  unfold representative
  simp only [literalComponent_eq table h]

theorem representative_first (v : Sector H B T)
    (h : ∃ w, EqvGen (Step table) v w ∧ P w) : P (representative table P Q v) := by
  apply prioritySet_first P Q _ (representative_mem table P Q v)
  simpa only [mem_literalComponent] using h

theorem representative_second (v : Sector H B T)
    (hp : ¬ ∃ w, EqvGen (Step table) v w ∧ P w)
    (hq : ∃ w, EqvGen (Step table) v w ∧ Q w) : Q (representative table P Q v) := by
  apply prioritySet_second P Q _ _ (representative_mem table P Q v)
  · simpa only [mem_literalComponent] using hp
  · simpa only [mem_literalComponent] using hq

end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
