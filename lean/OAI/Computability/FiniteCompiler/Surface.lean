import OAI.Computability.FiniteCompiler.Control

namespace OAI

/-!
Surface alphabet, preprocessing, and grading estimates.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation

/-- The complete head alphabet; internal control excludes raw, quota and cleanup. -/
inductive Head (H : Type*)
  | raw | pending | cleanup
  | internal : H → Head H
  deriving DecidableEq, Fintype

abbrev Sector (S Γ H : Type*) := Scan.Sector (Head H) (Base S) (Tag S Γ)
variable {S Γ H : Type*}
abbrev Cells (S Γ : Type*) := List (Base S × Tag S Γ)

/-- Literal clean-anchor slides, oriented to the leftmost reachable head gap. -/
inductive RawStep (blank : Γ) : Sector S Γ H → Sector S Γ H → Prop
  | slide (a : S) (l r : Cells S Γ) (lb rb : Bool) :
      RawStep blank ⟨Validator.cell blank (.anchor a)::l,.raw,r,lb,rb⟩
        ⟨l,.raw,Validator.cell blank (.anchor a)::r,lb,rb⟩

theorem rawStep_deterministic (blank : Γ) : Relator.RightUnique (RawStep (H := H) (S := S) blank) := by
  intro a b c hab hac
  cases hab; cases hac; rfl

def grade (v : Sector S Γ H) : ℕ :=
  Cleanup.cellsGrade v.left + 1 + Cleanup.cellsGrade v.right +
    (if v.leftBoundary then 1 else 0) + (if v.rightBoundary then 1 else 0)

theorem rawStep_grade (blank : Γ) {v w : Sector S Γ H} (h : RawStep blank v w) :
    grade v = grade w := by
  cases h
  simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]
  omega

theorem rawStep_skeleton (blank : Γ) {v w : Sector S Γ H} (h : RawStep blank v w) :
    Scan.baseSkeleton v = Scan.baseSkeleton w := by
  cases h
  simp [Scan.baseSkeleton,List.reverse_cons,List.append_assoc]

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

def rawSweep : Cells S Γ → Cells S Γ → Bool → Bool → Sector S Γ H
  | [],r,lb,rb => ⟨[],.raw,r,lb,rb⟩
  | (b,t)::l,r,lb,rb => match b with
    | .anchor _a => if t = clean blank then rawSweep l ((b,t)::r) lb rb
        else ⟨(b,t)::l,.raw,r,lb,rb⟩
    | _ => ⟨(b,t)::l,.raw,r,lb,rb⟩

theorem rawSweep_reaches (l r : Cells S Γ) (lb rb : Bool) :
    ReflTransGen (RawStep blank) (⟨l,.raw,r,lb,rb⟩ : Sector S Γ H) (rawSweep blank l r lb rb) := by
  induction l generalizing r with
  | nil => exact .refl
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b with
      | anchor a =>
          by_cases ht : t = clean blank
          · subst t
            simpa [rawSweep,Validator.cell] using
              (ReflTransGen.single (RawStep.slide a l r lb rb)).trans
                (ih (Validator.cell blank (.anchor a)::r))
          · simp only [rawSweep,ite_eq_right ht]
            exact .refl
      | cutC | cutD | workspace => exact .refl

theorem rawSweep_terminal (l r : Cells S Γ) (lb rb : Bool) :
    Terminal (RawStep (H := H) blank) (rawSweep blank l r lb rb) := by
  induction l generalizing r with
  | nil => intro w hw; cases hw
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b with
      | anchor a =>
          by_cases ht : t = clean blank
          · simp only [rawSweep,ite_eq_left ht]
            exact ih _
          · simp only [rawSweep,ite_eq_right ht]
            intro w hw
            cases hw
            exact ht rfl
      | cutC | cutD | workspace => intro w hw; cases hw

def rawNormal (v : Sector S Γ H) : Sector S Γ H :=
  match v.head with
  | .raw => rawSweep blank v.left v.right v.leftBoundary v.rightBoundary
  | _ => v

theorem rawNormal_reaches (v : Sector S Γ H) : ReflTransGen (RawStep blank) v (rawNormal blank v) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | raw => exact rawSweep_reaches blank l r a b
  | pending | cleanup | internal _ => exact .refl

theorem rawNormal_terminal (v : Sector S Γ H) : Terminal (RawStep blank) (rawNormal blank v) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | raw => exact rawSweep_terminal blank l r a b
  | pending | cleanup | internal _ => intro w hw; cases hw

theorem rawNormal_invariant {v w : Sector S Γ H} (h : EqvGen (RawStep blank) v w) :
    rawNormal blank v = rawNormal blank w := by
  apply terminal_unique (rawStep_deterministic blank) (rawNormal_terminal blank v) (rawNormal_terminal blank w)
  exact .trans _ _ _ (.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (rawNormal_reaches blank v)))
    (.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (rawNormal_reaches blank w)))

theorem rawNormal_grade (v : Sector S Γ H) : grade (rawNormal blank v) = grade v := by
  have aux : ∀ {a b : Sector S Γ H}, ReflTransGen (RawStep blank) a b → grade b = grade a := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ h ih => exact (rawStep_grade blank h).symm.trans ih
  exact aux (rawNormal_reaches blank v)

/-- Literal raw singleton; in particular no program is evaluated on it. -/
def raw (w : List S) : Sector S Γ H :=
  ⟨[],.raw,w.map (Validator.cell blank ∘ Base.anchor),true,true⟩

@[simp] theorem rawNormal_raw (w : List S) : rawNormal blank (raw (H := H) blank w) = raw blank w := rfl

theorem rawSweep_clean (w : List S) (r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H) blank (w.map (Validator.cell blank ∘ Base.anchor)) r lb rb =
      ⟨[],.raw,(w.reverse.map (Validator.cell blank ∘ Base.anchor))++r,lb,rb⟩ := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
      simp only [List.map_cons,Function.comp_apply,Validator.cell,rawSweep,↓reduceIte]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc,Validator.cell]

end

section
open Relation
variable {S Γ H : Type*} (blank : Γ)

/-- The quota rule is applicable only at the literal clean right cut. -/
inductive QuotaStep : Sector S Γ H → Sector S Γ H → Prop
  | trim (l r : Cells S Γ) (lb rb : Bool) :
      QuotaStep ⟨Validator.cell blank .workspace::l,.pending,
          Validator.cell blank .cutD::r,lb,rb⟩
        ⟨l,.pending,Validator.cell blank .cutD::r,lb,rb⟩

theorem quotaStep_deterministic : Relator.RightUnique (QuotaStep (S := S) (H := H) blank) := by
  intro a b c hab hac
  cases hab; cases hac; rfl

theorem quotaStep_grade {v w : Sector S Γ H} (h : QuotaStep blank v w) :
    grade v = grade w := by
  cases h
  simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]

theorem quotaStep_left {v w : Sector S Γ H} (h : QuotaStep blank v w) :
    ∃ l, v.left = Validator.cell blank .workspace::l := by
  cases h
  exact ⟨_,rfl⟩

variable [DecidableEq S] [DecidableEq Γ]

def trimQuota : Cells S Γ → Cells S Γ
  | [] => []
  | c::l => if c = Validator.cell blank .workspace then trimQuota l else c::l

theorem trimQuota_terminal (l : Cells S Γ) :
    ∀ r, trimQuota blank l ≠ Validator.cell blank .workspace::r := by
  induction l with
  | nil => intro r h; cases h
  | cons c l ih =>
      by_cases h : c = Validator.cell blank .workspace
      · simpa only [trimQuota,ite_eq_left h] using ih
      · simp only [trimQuota,ite_eq_right h]
        intro r hh
        exact h (List.cons.inj hh).1

def quotaNormal (v : Sector S Γ H) : Sector S Γ H :=
  match v.head,v.right with
  | .pending,d::_ => if d = Validator.cell blank .cutD then {v with left := trimQuota blank v.left} else v
  | _,_ => v

theorem trimQuota_reaches (l r : Cells S Γ) (lb rb : Bool) :
    ReflTransGen (QuotaStep blank)
      (⟨l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ : Sector S Γ H)
      ⟨trimQuota blank l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ := by
  induction l with
  | nil => exact .refl
  | cons c l ih =>
      by_cases h : c = Validator.cell blank .workspace
      · subst c
        simpa only [trimQuota,↓reduceIte] using (ReflTransGen.single (QuotaStep.trim l r lb rb)).trans ih
      · simpa only [trimQuota,ite_eq_right h] using
          (ReflTransGen.refl : ReflTransGen (QuotaStep blank)
            (⟨c::l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ : Sector S Γ H) _)

theorem quotaNormal_reaches (v : Sector S Γ H) :
    ReflTransGen (QuotaStep blank) v (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | pending =>
      cases r with
      | nil => exact .refl
      | cons d r =>
          by_cases h : d = Validator.cell blank .cutD
          · subst d
            simpa only [quotaNormal,↓reduceIte] using trimQuota_reaches blank l r lb rb
          · simp only [quotaNormal,ite_eq_right h]
            exact .refl
  | raw | cleanup | internal _ => exact .refl

theorem quotaNormal_terminal (v : Sector S Γ H) : Terminal (QuotaStep blank) (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | pending =>
      cases r with
      | nil => intro z hz; cases hz
      | cons d r =>
          by_cases h : d = Validator.cell blank .cutD
          · subst d
            simp only [quotaNormal,↓reduceIte]
            intro z hz
            obtain ⟨l',hl⟩ := quotaStep_left blank hz
            exact trimQuota_terminal blank l l' hl
          · simp only [quotaNormal,ite_eq_right h]
            intro z hz
            cases hz
            exact h rfl
  | raw | cleanup | internal _ => intro z hz; cases hz

theorem quotaNormal_invariant {v w : Sector S Γ H} (h : EqvGen (QuotaStep blank) v w) :
    quotaNormal blank v = quotaNormal blank w := by
  apply terminal_unique (quotaStep_deterministic blank) (quotaNormal_terminal blank v) (quotaNormal_terminal blank w)
  exact .trans _ _ _ (.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (quotaNormal_reaches blank v)))
    (.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (quotaNormal_reaches blank w)))

theorem quotaNormal_grade (v : Sector S Γ H) : grade (quotaNormal blank v) = grade v := by
  have aux : ∀ {a b : Sector S Γ H}, ReflTransGen (QuotaStep blank) a b → grade b = grade a := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ h ih => exact (quotaStep_grade blank h).symm.trans ih
  exact aux (quotaNormal_reaches blank v)

/-- Unmerge after trimming. The outer boundaries may be absent and the outer
    cells may be arbitrarily dirty. Only the two displayed cut cells are tested. -/
def unmerge (v : Sector S Γ H) : List (Sector S Γ H) :=
  match v.left,v.head,v.right with
  | c::l,.pending,d::r =>
    if c = Validator.cell blank .cutC ∧ d = Validator.cell blank .cutD then
      [rawNormal blank ⟨l,.raw,[],v.leftBoundary,true⟩,
        rawNormal blank ⟨[],.raw,r,true,v.rightBoundary⟩]
    else [v]
  | _,_,_ => [v]

def pendingPreprocess (v : Sector S Γ H) : List (Sector S Γ H) :=
  unmerge blank (quotaNormal blank v)

theorem pendingPreprocess_invariant {v w : Sector S Γ H} (h : EqvGen (QuotaStep blank) v w) :
    pendingPreprocess blank v = pendingPreprocess blank w := by
  simp only [pendingPreprocess,quotaNormal_invariant blank h]

def listGrade (l : List (Sector S Γ H)) : ℕ := (l.map grade).sum

theorem unmerge_grade (v : Sector S Γ H) : listGrade (unmerge blank v) = grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l with
  | nil => rfl
  | cons c l =>
      cases q with
      | pending =>
          cases r with
          | nil => rfl
          | cons d r =>
              by_cases h : c = Validator.cell blank .cutC ∧ d = Validator.cell blank .cutD
              · rcases h with ⟨rfl,rfl⟩
                simp [unmerge,listGrade,rawNormal_grade]
                simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]
                omega
              · simp [unmerge,h,listGrade]
      | raw | cleanup | internal _ => simp [unmerge,listGrade]

theorem pendingPreprocess_grade (v : Sector S Γ H) :
    listGrade (pendingPreprocess blank v) = grade v := by
  rw [pendingPreprocess,unmerge_grade,quotaNormal_grade]

theorem trimQuota_workspace (s : ℕ) (l : Cells S Γ) :
    trimQuota blank (List.replicate s (Validator.cell blank .workspace) ++ l) = trimQuota blank l := by
  induction s with
  | zero => rfl
  | succ s ih => simpa [List.replicate_succ,trimQuota] using ih

/-- The literal merge is undone, even on dirty/incomplete surroundings. -/
theorem pendingPreprocess_merge (l r : Cells S Γ) (s : ℕ) (lb rb : Bool) :
    pendingPreprocess (H := H) blank
      ⟨List.replicate s (Validator.cell blank .workspace) ++ Validator.cell blank .cutC::l,
        .pending,Validator.cell blank .cutD::r,lb,rb⟩ =
      [rawNormal blank ⟨l,.raw,[],lb,true⟩,rawNormal blank ⟨[],.raw,r,true,rb⟩] := by
  simp only [pendingPreprocess,quotaNormal]
  rw [trimQuota_workspace]
  simp [trimQuota,unmerge,Validator.cell]

end

open Relation
variable {S Γ H : Type*}

def cleanupHead : Cleanup.Head → Head H
  | .cleanup => .cleanup
  | .raw => .raw

def ofCleanup (v : Cleanup.Sector S Γ) : Sector S Γ H := Scan.mapHead cleanupHead v

def cleanupNormal (blank : Γ) (v : Sector S Γ H) : Sector S Γ H :=
  match v.head with
  | .cleanup => ofCleanup (Cleanup.normal blank
      ⟨v.left,.cleanup,v.right,v.leftBoundary,v.rightBoundary⟩)
  | _ => v

@[simp] theorem cleanupNormal_ofCleanup (blank : Γ) (v : Cleanup.Sector S Γ) :
    cleanupNormal blank (ofCleanup (H := H) v) = ofCleanup (Cleanup.normal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl

theorem cleanupNormal_grade (blank : Γ) (v : Sector S Γ H) :
    grade (cleanupNormal blank v) ≤ grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | cleanup =>
      have h := Cleanup.output_grade_le blank l.reverse
      rw [Cleanup.cellsGrade_reverse] at h
      simp only [cleanupNormal,Cleanup.normal,ofCleanup,Scan.mapHead,grade,
        Cleanup.cellsGrade_append]
      simp only [Cleanup.cellsGrade,List.map_nil,List.sum_nil] at h ⊢
      cases lb <;> cases rb <;> simp_all
      all_goals omega
  | raw | pending | internal _ => exact le_rfl

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

def cleanupPreprocess (v : Sector S Γ H) : Sector S Γ H :=
  rawNormal blank (cleanupNormal blank v)

theorem cleanupPreprocess_grade (v : Sector S Γ H) :
    grade (cleanupPreprocess blank v) ≤ grade v := by
  rw [cleanupPreprocess,rawNormal_grade]
  exact cleanupNormal_grade blank v

@[simp] theorem cleanupPreprocess_ofCleanup (v : Cleanup.Sector S Γ) :
    cleanupPreprocess blank (ofCleanup (H := H) v) =
      rawNormal blank (ofCleanup (Cleanup.normal blank v)) := by
  rw [cleanupPreprocess,cleanupNormal_ofCleanup]

theorem cleanupPreprocess_invariant {v w : Cleanup.Sector S Γ}
    (h : EqvGen (Cleanup.Step blank) v w) :
    cleanupPreprocess blank (ofCleanup (H := H) v) = cleanupPreprocess blank (ofCleanup w) := by
  simp only [cleanupPreprocess_ofCleanup,Cleanup.normal_invariant blank h]

theorem cleanupPreprocess_rawStep {v w : Sector S Γ H} (h : RawStep blank v w) :
    cleanupPreprocess blank v = cleanupPreprocess blank w := by
  cases h
  apply rawNormal_invariant blank
  exact .rel _ _ (.slide _ _ _ _ _)

/-- Successful cleanup is exactly a full raw singleton, without any call to
    the program on the returned string. -/
theorem cleanupPreprocess_success (l : Cells S Γ) (out : List S) (n : ℕ)
    (h : Simulator.anchorView l = out.map some ++ List.replicate n none) :
    cleanupPreprocess (H := H) blank ⟨l.reverse,.cleanup,[],true,true⟩ = raw blank out := by
  have he := Cleanup.emit_returned l out n h
  simp [cleanupPreprocess,cleanupNormal,Cleanup.normal,ofCleanup,Scan.mapHead,
    cleanupHead,Cleanup.output,he,rawNormal,rawSweep,raw,Cleanup.letter,Validator.cell]

@[simp] theorem cleanupPreprocess_raw (w : List S) :
    cleanupPreprocess blank (raw (H := H) blank w) = raw blank w := rfl

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Control
open Relation
variable {S Γ Q : Type*}

/-- Literal entry and successful exit tests, both finite data predicates. -/
def Entry (blank : Γ) (v : Sector S Γ Q) : Prop :=
  v.head = .initial ∧ v.right.head? = some (Validator.cell blank .cutD)

def Success (v : Sector S Γ Q) : Prop :=
  v.head = .machine .ok ∧ v.right = [] ∧ v.rightBoundary = true

instance entryDecidable (blank : Γ) [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] :
    DecidablePred (Entry (S := S) (Q := Q) blank) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

instance successDecidable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] :
    DecidablePred (Success (S := S) (Γ := Γ) (Q := Q)) := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem entry_cases (blank : Γ) {v : Sector S Γ Q} (h : Entry blank v) :
    ∃ w : Validator.Sector S Γ, Validator.Entry blank w ∧ v = validator w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  obtain ⟨rfl,hr⟩ := h
  refine ⟨⟨.initial,l,r,lb,rb⟩,⟨rfl,?_⟩,rfl⟩
  cases r with
  | nil => cases hr
  | cons d r => exact ⟨r,by simpa using hr⟩

theorem entry_validator (blank : Γ) {w : Validator.Sector S Γ} (h : Validator.Entry blank w) :
    Entry blank (validator (Q := Q) w) := by
  rcases w with ⟨q,l,r,lb,rb⟩
  obtain ⟨rfl,r,rfl⟩ := h
  exact ⟨rfl,rfl⟩

theorem success_cases {v : Sector S Γ Q} (h : Success v) :
    ∃ w : Compiled.MachineSector S Γ Q, w.head = .ok ∧ w.right = [] ∧
      w.rightBoundary = true ∧ v = machine w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  obtain ⟨rfl,rfl,rfl⟩ := h
  exact ⟨⟨l,.ok,[],lb,true⟩,rfl,rfl,rfl,rfl⟩

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem entries_unique {v w : Sector S Γ Q} (hv : Entry A.blank v) (hw : Entry A.blank w)
    (h : EqvGen (Scan.Step (table A M)) v w) : v = w := by
  obtain ⟨v,hve,rfl⟩ := entry_cases A.blank hv
  obtain ⟨w,hwe,rfl⟩ := entry_cases A.blank hw
  have hc := cfg_connected A M h
  rw [cfg_validator,cfg_validator] at hc
  exact congrArg validator (Compiled.entries_unique A M hve hwe hc)

theorem successes_unique {v w : Sector S Γ Q} (hv : Success v) (hw : Success w)
    (h : EqvGen (Scan.Step (table A M)) v w) : v = w := by
  obtain ⟨v,hve,_,_,rfl⟩ := success_cases hv
  obtain ⟨w,hwe,_,_,rfl⟩ := success_cases hw
  have hc := cfg_connected A M h
  rw [cfg_machine,cfg_machine] at hc
  exact congrArg machine (Compiled.ok_unique A M hve hwe hc)

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Sector S Γ Q)]

def representative (v : Sector S Γ Q) : Sector S Γ Q :=
  Scan.representative (table A M) (Entry A.blank) Success v

theorem representative_connected (v : Sector S Γ Q) :
    EqvGen (Scan.Step (table A M)) v (representative A M v) :=
  Scan.representative_connected _ _ _ v

theorem representative_eq {v w : Sector S Γ Q}
    (h : EqvGen (Scan.Step (table A M)) v w) : representative A M v = representative A M w :=
  Scan.representative_eq _ _ _ h

theorem representative_entry {v : Sector S Γ Q} (hv : Entry A.blank v) :
    representative A M v = v := by
  apply (entries_unique A M hv _ (representative_connected A M v)).symm
  exact Scan.representative_first _ _ _ v ⟨v,.refl _,hv⟩

theorem representative_success {v : Sector S Γ Q} (hv : Success v)
    (hn : ¬ ∃ w, EqvGen (Scan.Step (table A M)) v w ∧ Entry A.blank w) :
    representative A M v = v := by
  apply (successes_unique A M hv _ (representative_connected A M v)).symm
  exact Scan.representative_second _ _ _ v hn ⟨v,.refl _,hv⟩

end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- Internal finite-component search, with entry priority. No invocation of the
    compiled machine as an evaluator occurs here. -/
def internalPreprocess (v : Control.Sector S Γ Q) : List (Sector S Γ (Control.Head S Q)) :=
  let w := Control.representative A M v
  if Control.Entry A.blank w then
    pendingPreprocess A.blank ⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩
  else if Control.Success w then
    [cleanupPreprocess A.blank ⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩]
  else [Scan.mapHead Head.internal w]

theorem internalPreprocess_invariant {v w : Control.Sector S Γ Q}
    (h : EqvGen (Scan.Step (Control.table A M)) v w) :
    internalPreprocess A M v = internalPreprocess A M w := by
  simp only [internalPreprocess,Control.representative_eq A M h]

theorem internalPreprocess_entry (v : Control.Sector S Γ Q) (hv : Control.Entry A.blank v) :
    internalPreprocess A M v = pendingPreprocess A.blank
      ⟨v.left,.pending,v.right,v.leftBoundary,v.rightBoundary⟩ := by
  simp only [internalPreprocess,Control.representative_entry A M hv,ite_eq_left hv]

theorem internalPreprocess_success (v : Control.Sector S Γ Q) (hv : Control.Success v)
    (hn : ¬ ∃ w, EqvGen (Scan.Step (Control.table A M)) v w ∧ Control.Entry A.blank w) :
    internalPreprocess A M v =
      [cleanupPreprocess A.blank ⟨v.left,.cleanup,v.right,v.leftBoundary,v.rightBoundary⟩] := by
  have he : ¬ Control.Entry A.blank v := fun h => hn ⟨v,.refl _,h⟩
  simp only [internalPreprocess,Control.representative_success A M hv hn,ite_eq_right he,ite_eq_left hv]

/-- Complete sector preprocessing, prior to the only partial operation: maximal
    full-raw-run evaluation. Headless sectors will be preserved by the parser. -/
def preprocess (v : Sector S Γ (Control.Head S Q)) : List (Sector S Γ (Control.Head S Q)) :=
  match v.head with
  | .raw => [rawNormal A.blank v]
  | .pending => pendingPreprocess A.blank v
  | .cleanup => [cleanupPreprocess A.blank v]
  | .internal q => internalPreprocess A M ⟨v.left,q,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem preprocess_raw (w : List S) : preprocess A M (raw A.blank w) = [raw A.blank w] := rfl

end

open Relation
variable {S Γ H H' : Type*}

def skeletonGrade (s : List (Base S) × Bool × Bool) : ℕ :=
  (s.1.map Cleanup.grade).sum + 1 + (if s.2.1 then 1 else 0) + (if s.2.2 then 1 else 0)

theorem grade_skeleton (v : Sector S Γ H) : grade v = skeletonGrade (Scan.baseSkeleton v) := by
  simp [grade,skeletonGrade,Scan.baseSkeleton,Cleanup.cellsGrade,List.map_reverse,
    List.map_append,List.map_map]
  omega

theorem grade_eq_of_skeleton {v : Sector S Γ H} {w : Sector S Γ H'}
    (h : Scan.baseSkeleton v = Scan.baseSkeleton w) : grade v = grade w := by
  rw [grade_skeleton,grade_skeleton,h]

variable {Q : Type*} (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem internalPreprocess_grade (v : Control.Sector S Γ Q) :
    listGrade (internalPreprocess A M v) ≤ grade (Scan.mapHead Head.internal v) := by
  have he : grade (Scan.mapHead Head.internal (Control.representative A M v)) =
      grade (Scan.mapHead Head.internal v) := by
    apply grade_eq_of_skeleton
    simp only [Scan.skeleton_mapHead]
    exact (Scan.connected_skeleton _ (Control.representative_connected A M v)).symm
  unfold internalPreprocess
  dsimp only
  split
  · rw [pendingPreprocess_grade]
    exact he.le
  · split
    · simp only [listGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      exact (cleanupPreprocess_grade A.blank _).trans he.le
    · simpa only [listGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he.le

theorem preprocess_grade (v : Sector S Γ (Control.Head S Q)) :
    listGrade (preprocess A M v) ≤ grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw => simp [preprocess,listGrade,rawNormal_grade]
  | pending => exact (pendingPreprocess_grade A.blank _).le
  | cleanup => exact cleanupPreprocess_grade A.blank _
  | internal q => exact internalPreprocess_grade A M ⟨l,q,r,lb,rb⟩

theorem preprocess_rawStep {v w : Sector S Γ (Control.Head S Q)} (h : RawStep A.blank v w) :
    preprocess A M v = preprocess A M w := by
  cases h
  exact congrArg (fun x => [x]) (rawNormal_invariant A.blank (.rel _ _ (.slide _ _ _ _ _)))

theorem preprocess_quotaStep {v w : Sector S Γ (Control.Head S Q)} (h : QuotaStep A.blank v w) :
    preprocess A M v = preprocess A M w := by
  cases h
  exact pendingPreprocess_invariant A.blank (.rel _ _ (.trim _ _ _ _))

@[simp] theorem preprocess_ofCleanup (v : Cleanup.Sector S Γ) :
    preprocess A M (ofCleanup v) = [cleanupPreprocess A.blank (ofCleanup v)] := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl

theorem preprocess_cleanupStep {v w : Cleanup.Sector S Γ} (h : Cleanup.Step A.blank v w) :
    preprocess A M (ofCleanup v) = preprocess A M (ofCleanup w) := by
  simp only [preprocess_ofCleanup,cleanupPreprocess_invariant A.blank (.rel _ _ h)]

theorem preprocess_entryStep (l r : Cells S Γ) (lb rb : Bool) :
    preprocess A M ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩ =
    preprocess A M ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩ := by
  exact (internalPreprocess_entry A M
    (⟨l,.initial,Validator.cell A.blank .cutD::r,lb,rb⟩ : Control.Sector S Γ Q) ⟨rfl,rfl⟩).symm

theorem preprocess_internalStep {v w : Control.Sector S Γ Q}
    (h : Scan.Step (Control.table A M) v w) :
    preprocess A M (Scan.mapHead Head.internal v) = preprocess A M (Scan.mapHead Head.internal w) := by
  rcases v with ⟨l,q,r,a,b⟩
  rcases w with ⟨l',q',r',a',b'⟩
  change internalPreprocess A M ⟨l,q,r,a,b⟩ = internalPreprocess A M ⟨l',q',r',a',b'⟩
  exact internalPreprocess_invariant A M (.rel _ _ h)

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
/-- The two outputs of unmerging a *clean full* entry are precisely the two
    full raw words. This includes zero workspace and empty x or y. -/
theorem pendingPreprocess_cleanEntry (x y : List S) (s : ℕ) :
    pendingPreprocess (H := Control.Head S Q) A.blank
      ⟨(Compiled.cleanEntry A.blank x y s).left,.pending,
        (Compiled.cleanEntry A.blank x y s).right,true,true⟩ =
      [raw A.blank x,raw A.blank y] := by
  rw [Compiled.cleanEntry,pendingPreprocess_merge]
  change [rawSweep A.blank ((x.map (Validator.cell A.blank ∘ Base.anchor)).reverse) [] true true,
    raw A.blank y] = [raw A.blank x,raw A.blank y]
  rw [← List.map_reverse,rawSweep_clean]
  simp [raw]

end FiniteAlgebraicEnvelopes.Compiler.Surface

/- Literal path alphabet and sector parsing for the finite compiler.
   All definitions are independent of the partial program. -/

end OAI
