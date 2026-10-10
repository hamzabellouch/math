import Mathlib
import OAI.Computability.FiniteCompiler.Paths
import OAI.Computability.FiniteCompiler.Selectors
import OAI.Computability.FiniteCompiler.UniformControl
import OAI.Computability.FiniteCompiler.UniformMachines
import OAI.Computability.FiniteCompiler.UniformPaths
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.BooneHigman.Contracted
import OAI.GroupTheory.SimpleOvergroups.TruncatedAlgebra

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.WordCalculus
noncomputable section
variable {M N : Type*} [Monoid M] [Monoid N] {m : ℕ}

def retract (C : WordCalculus M m) (r : N →* M) (i : M →* N)
    (hi : ∀ x, r (i x) = x) (grade : N → ℕ)
    (hg1 : grade 1 = 0) (hgm : ∀ x y, grade (x*y) = grade x + grade y)
    (hgi : ∀ x, grade (i x) = C.grade x)
    (hgr : ∀ x, C.grade (r x) ≤ grade x) : WordCalculus N m where
  grade := grade
  grade_one := hg1
  grade_mul := hgm
  omega := i C.omega
  grade_omega := (hgi _).trans C.grade_omega
  omega_ne_one h := C.omega_ne_one (by simpa only [hi, map_one] using congrArg r h)
  normal x := i (C.normal (r x))
  normal_one := by simp only [map_one, C.normal_one]
  normal_omega := by simp only [hi, C.normal_omega]
  nonincreasing x hx := by
    rw [hgi]
    exact (C.nonincreasing _ ((hgr _).trans hx)).trans (hgr _)
  idempotent x hx := by rw [hi, C.idempotent _ ((hgr _).trans hx)]
  context h a b hu hv := by
    have he := congrArg r h
    simp only [hi] at he
    apply congrArg i
    simp only [map_mul]
    apply C.context he (r a) (r b)
    · simpa only [map_mul] using (hgr _).trans hu
    · simpa only [map_mul] using (hgr _).trans hv
  absorbs a b := by simp only [map_mul, hi, C.absorbs]

end
end SimpleFInftyOvergroups.BoundedEncoding.WordCalculus

namespace SimpleFInftyOvergroups.CommonCompiler
noncomputable section
open FiniteAlgebraicEnvelopes
open Compiler MachineRealization
open scoped Classical Compiler.HeadCodec

variable {T Γ Q : Type*}
abbrev Letter (T Γ Q : Type*) := Compiler.Word.Letter T (Bool × Γ) (ParameterCode.Control Q)
abbrev FiniteLetter (T Γ Q : Type*) (n : ℕ) :=
  Compiler.Word.Letter T (Bool × Γ) (ParameterMachine.State Q n)

abbrev includeLetter (n : ℕ) : FiniteLetter T Γ Q n → Letter T Γ Q :=
  Word.letterMap (ParameterCode.encode n)

theorem includeLetter_injective (n : ℕ) :
    Function.Injective (includeLetter (T:=T) (Γ:=Γ) (Q:=Q) n) :=
  Word.letterMap_injective _ (ParameterCode.encode_injective n)

def retractLetter (n : ℕ) (a : Letter T Γ Q) : FiniteLetter T Γ Q n :=
  if h : ∃ b, includeLetter n b = a then h.choose else .zero

@[simp] theorem retract_include (n : ℕ) (a : FiniteLetter T Γ Q n) :
    retractLetter n (includeLetter n a) = a := by
  have h : ∃ b, includeLetter n b = includeLetter n a := ⟨a,rfl⟩
  rw [retractLetter, dite_eq_left h]
  exact includeLetter_injective n h.choose_spec

theorem grade_include_letter (n : ℕ) (a : FiniteLetter T Γ Q n) :
    Path.letterGrade Word.gradeCell (includeLetter n a) =
      Path.letterGrade Word.gradeCell a := by
  cases a <;> rfl

theorem grade_include (n : ℕ) (w : List (FiniteLetter T Γ Q n)) :
    Word.grade (w.map (includeLetter n)) = Word.grade w := by
  simp only [Word.grade, Path.grade, List.map_map]
  congr 2
  funext a
  exact grade_include_letter n a

theorem grade_retract_letter (n : ℕ) (a : Letter T Γ Q) :
    Path.letterGrade Word.gradeCell (retractLetter n a) ≤
      Path.letterGrade Word.gradeCell a := by
  rw [retractLetter]
  split
  · rename_i h
    exact le_of_eq ((grade_include_letter n h.choose).symm.trans
      (congrArg (Path.letterGrade Word.gradeCell) h.choose_spec))
  · exact Nat.zero_le _

theorem grade_retract (n : ℕ) (w : List (Letter T Γ Q)) :
    Word.grade (w.map (retractLetter n)) ≤ Word.grade w := by
  induction w with
  | nil => exact le_refl 0
  | cons a w ih => exact Nat.add_le_add (grade_retract_letter n a) ih

abbrev includeWord (n : ℕ) : FreeMonoid (FiniteLetter T Γ Q n) →* FreeMonoid (Letter T Γ Q) :=
  FreeMonoid.map (includeLetter n)
abbrev retractWord (n : ℕ) : FreeMonoid (Letter T Γ Q) →* FreeMonoid (FiniteLetter T Γ Q n) :=
  FreeMonoid.map (retractLetter n)

@[simp] theorem retract_include_word (n : ℕ) (w : FreeMonoid (FiniteLetter T Γ Q n)) :
    retractWord n (includeWord n w) = w := by
  apply FreeMonoid.toList.injective
  simp only [includeWord,retractWord,FreeMonoid.toList_map,List.map_map,
    Function.comp_def,retract_include]
  exact List.map_id _

variable [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]

def clamp (n : ℕ) (a : Letter T Γ Q) : Letter T Γ Q :=
  if a ∈ ParameterCode.letters n then a else .zero

omit [Primcodable Q] in
@[simp] theorem include_retract [Primcodable Q] (n : ℕ) (a : Letter T Γ Q) :
    includeLetter n (retractLetter n a) = clamp n a := by
  by_cases h : ∃ b, includeLetter n b = a
  · rw [retractLetter,dite_eq_left h,clamp,ite_eq_left ((ParameterCode.mem_letters_iff n a).mpr h)]
    exact h.choose_spec
  · rw [retractLetter,dite_eq_right h,clamp,ite_eq_right (fun ha => h ((ParameterCode.mem_letters_iff n a).mp ha))]
    rfl

theorem clamp_words (n : ℕ) (w : List (Letter T Γ Q)) :
    (w.map (retractLetter n)).map (includeLetter n) = w.map (clamp n) := by
  simp only [List.map_map,Function.comp_def,include_retract]

variable [Primcodable Γ] [Primcodable T]

omit [Primcodable Γ] [Primcodable T] in
theorem primrec_clamp [Primcodable Γ] [Primcodable T] :
    Primrec₂ (clamp (T:=T) (Γ:=Γ) (Q:=Q)) := by
  exact (Primrec.ite
    (Bootstrap.Selectors.primrec_mem.comp Primrec.snd
      (ParameterCode.primrec_letters.comp Primrec.fst))
    Primrec.snd (Primrec.const (Path.Letter.zero : Letter T Γ Q))).of_eq (by
      intro x
      simp only [clamp]
      split <;> simp_all)

omit [Fintype Q] [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
    [Primcodable Γ] [Primcodable T] in
theorem primrec_letterGrade [Fintype Q] [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
    [Primcodable Γ] [Primcodable T] :
    Primrec (Path.letterGrade Word.gradeCell : Letter T Γ Q → ℕ) := by
  exact ((Effect.primrec_sumElim
    (Primrec.dom_finite (fun i : Fin 3 => if i = 0 then 0 else 1))
    (Effect.primrec_sumElim (Primrec.dom_finite Word.gradeCell)
      (Effect.primrec_sumElim (Primrec.dom_finite Word.gradeCell) (Primrec.const 1)))).comp
        HeadCodec.primrec_pathCode).of_eq (fun a => by cases a <;> rfl)

theorem primrec_grade : Primrec (Word.grade (S:=T) (Γ:=Bool × Γ) (Q:=ParameterCode.Control Q)) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (primrec_letterGrade.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq (by
        intro w
        induction w with
        | nil => rfl
        | cons a w ih => simpa only [id_eq, List.foldr_cons, Word.grade, Path.grade_cons] using
          (congrArg (Path.letterGrade Word.gradeCell a + ·) ih))

variable {S : Type*} (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  (p : S) (B : Simulator.Alphabet T (Bool × Γ))

def service (f : ℕ × List T → Part (List T)) (x : ℕ × List (Letter T Γ Q)) :
    Part (List (Letter T Γ Q)) :=
  ParameterCode.codedNormal A M p B f (x.1, x.2.map (clamp x.1))

theorem partrec_service {f : ℕ × List T → Part (List T)} (hf : Partrec f) :
    Partrec (service A M p B f) := by
  exact (ParameterCode.partrec_codedNormal A M p B hf).comp
    (Primrec.fst.pair (Primrec.list_map Primrec.snd
      (primrec_clamp.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)).to_comp

def calculus (n : ℕ)
    (decode : ∀ g a, B.output g = some a → g = B.input a)
    {f : ℕ × List T → Part (List T)} {m : ℕ}
    (budget : PartialBudget (fun w => f (n,w)) m)
    (realizes : Word.Realizes B (ParameterMachine.machine A M p n) (fun w => f (n,w))) :
    BoundedEncoding.WordCalculus (FreeMonoid (Letter T Γ Q)) m := by
  letI := ParameterCode.finiteOrder (T:=T) (Γ:=Γ) (Q:=Q) n
  let C := BoundedEncoding.CompilerCalculus.calculus B (ParameterMachine.machine A M p n)
    decode budget realizes
  exact C.retract (retractWord n) (includeWord n) (retract_include_word n)
    (fun w => Word.grade w.toList) rfl (fun _ _ => Word.grade_append _ _)
    (fun w => grade_include n w.toList) (fun w => grade_retract n w.toList)

omit [Primcodable Γ] [Primcodable T] in
theorem service_full [Primcodable Γ] [Primcodable T] (n : ℕ)
    (decode : ∀ g a, B.output g = some a → g = B.input a)
    {f : ℕ × List T → Part (List T)} {m : ℕ}
    (budget : PartialBudget (fun w => f (n,w)) m)
    (realizes : Word.Realizes B (ParameterMachine.machine A M p n) (fun w => f (n,w)))
    (w : List (Letter T Γ Q)) (hw : Word.grade w ≤ m) :
    ((calculus A M p B n decode budget realizes).normal (FreeMonoid.ofList w)).toList ∈
      service A M p B f (n,w) := by
  let := ParameterCode.finiteOrder (T:=T) (Γ:=Γ) (Q:=Q) n
  rw [service,← clamp_words,ParameterCode.codedNormal_map,
    Word.partialNormal_eq_some B (ParameterMachine.machine A M p n) budget _
      ((grade_retract n w).trans hw)]
  exact (Part.mem_map_iff _).mpr ⟨_, Part.mem_some _, rfl⟩

end
end SimpleFInftyOvergroups.CommonCompiler

end OAI
