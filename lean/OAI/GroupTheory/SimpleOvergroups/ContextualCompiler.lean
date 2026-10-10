import Mathlib
import OAI.Computability.FiniteCompiler.TapeFolding
import OAI.GroupTheory.SimpleOvergroups.BoundedFamilyTests
import OAI.GroupTheory.SimpleOvergroups.CommonCompiler
import OAI.GroupTheory.SimpleOvergroups.DoubleEffective
import OAI.GroupTheory.SimpleOvergroups.FamilyProgram
import OAI.GroupTheory.SimpleOvergroups.EffectiveFamilies

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding.Source
noncomputable section
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open BoundedEncoding NamedAction
open scoped Classical Compiler.HeadCodec

abbrev Sigma := ThreeCodes.Alphabet

def rel (a b : Sigma) : Prop := Encodable.encode a < Encodable.encode b
local instance : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ < _))
local instance : Std.Trichotomous rel := ⟨fun a b hab hba => by
  apply Encodable.encode_injective
  change ¬Encodable.encode a < Encodable.encode b at hab
  change ¬Encodable.encode b < Encodable.encode a at hba
  omega⟩
theorem wf_rel : WellFounded rel := InvImage.wf Encodable.encode Nat.lt_wfRel.wf

theorem primrec_shortlex : PrimrecRel (List.Shortlex rel) := by
  let ord : LinearOrder Sigma := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  exact @Search.primrec_shortlex _ _ _ ord ⟨inferInstance, Primrec.dom_finite _⟩

def raw (n : ℕ) (w : List Sigma) : Part (List Sigma) :=
  WordProgramming.eval ((Encodable.decode n : Option Nat.Partrec.Code).getD .zero) w

theorem raw_encode (c : Nat.Partrec.Code) : raw (Encodable.encode c) = WordProgramming.eval c := by
  funext w
  simp [raw]

theorem partrec_raw : Partrec₂ raw :=
  WordProgramming.partrec_eval.comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const .zero)).to_comp Computable.snd

abbrev terminalAlphabet {Γ : Type*} (A : Alphabet (Sigma ⊕ Unit) Γ) :=
  UniversalMachine.restrict (ParameterMachine.alphabet A)
abbrev terminalMachine {Γ Q : Type*} [DecidableEq Γ] (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ) (n : ℕ) :=
  ParameterMachine.machine A M (.inr ()) n

structure Family where
  Γ : Type
  Q : Type
  [finiteΓ : Fintype Γ]
  [finiteQ : Fintype Q]
  [decΓ : DecidableEq Γ]
  [decQ : DecidableEq Q]
  [codeΓ : Primcodable Γ]
  [codeQ : Primcodable Q]
  A : Alphabet (Sigma ⊕ Unit) Γ
  M : Machine Q Γ
  decode : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a
  realizes : ∀ n, Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n)

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

theorem exists_family : Nonempty Family := by
  obtain ⟨Γ,Q,hΓ,hQ,dΓ,A,M,hd,hr⟩ := UniversalMachine.exists_parameter_machine partrec_raw
  let : Fintype Γ := hΓ
  let : Fintype Q := hQ
  let : DecidableEq Γ := dΓ
  let : Primcodable Γ := Effect.finitePrimcodable Γ
  let : Primcodable Q := Effect.finitePrimcodable Q
  exact ⟨⟨Γ,Q,A,M,UniversalMachine.restrict_decode (ParameterMachine.alphabet A)
    (ParameterMachine.output_decode A hd),hr⟩⟩

def family : Family := exists_family.some

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q P₁ P₂ : Type} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance : Primcodable (ZMod 2) := Effect.finitePrimcodable _
local instance : Primcodable (ZMod 3) := Effect.finitePrimcodable _

abbrev Syntax := CommonCompiler.Letter Sigma Γ Q
abbrev Acting := EffectiveNames.Double.G₂ P₁ P₂ (ZMod 2) (Syntax (Γ:=Γ) (Q:=Q)) 7
abbrev Points := EffectiveNames.Double.X₂ P₁ P₂ (ZMod 2) (Syntax (Γ:=Γ) (Q:=Q)) 7
local instance : Primcodable (Syntax (Γ:=Γ) (Q:=Q)) := inferInstance
local instance : Primcodable (Acting (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂)) := inferInstance
local instance : Primcodable (Points (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂)) := inferInstance

abbrev ops := EffectiveNames.Double.operations (P₁:=P₁) (P₂:=P₂) (k₀:=ZMod 2) (n:=7)
  (Word.grade (S:=Sigma) (Γ:=Bool × Γ) (Q:=ParameterCode.Control Q))

abbrev Symbols (k : ℕ) : Fin 3 → Type _
  | 0 => Fin k × Bool
  | 1 => ProductFamily.Letter (Syntax (Γ:=Γ) (Q:=Q))
  | 2 => NamedAction.Letter (Acting (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂))
      (Points (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂))

abbrev Keys (k : ℕ) : Fin 3 → Type _
  | 0 => List (Fin k × Bool)
  | 1 => ProductFamily.Key (Syntax (Γ:=Γ) (Q:=Q))
  | 2 => List ℕ × (ℕ × ℕ) × List ℕ

local instance (i : Fin 3) : Primcodable (Symbols (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) k i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
local instance (i : Fin 3) : Primcodable (Keys (Γ:=Γ) (Q:=Q) k i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

def cost : (i : Fin 3) → Symbols (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) k i → ℕ
  | 0 => fun _ => 0
  | 1 => ProductFamily.cost (Path.letterGrade Word.gradeCell)
  | 2 => (ops (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂)).letterCost

def code (i : Fin 3) := ThreeCodes.code i (cost (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k) i)
def search (i : Fin 3) := ThreeCodes.search i (cost (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k) i)

omit [Finite P₁] [Finite P₂] in
theorem primrec_cost (i : Fin 3) : Primrec (cost (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k) i) := by
  fin_cases i
  · exact Primrec.const 0
  · exact ProductFamily.primrec_cost (A:=Syntax (Γ:=Γ) (Q:=Q))
      (CommonCompiler.primrec_letterGrade (T:=Sigma) (Γ:=Γ) (Q:=Q))
  · exact EffectiveNames.Double.primrec_cost (P₁:=P₁) (P₂:=P₂) (k₀:=ZMod 2) (n:=7)
      (Word.grade (S:=Sigma) (Γ:=Bool × Γ) (Q:=ParameterCode.Control Q))
      (CommonCompiler.primrec_grade (T:=Sigma) (Γ:=Γ) (Q:=Q))

variable (e₁ : P₁ → EffectiveNames.Enlargement.Coeff.Name (ZMod 2))
  (e₂ : P₂ → EffectiveNames.Enlargement.Coeff.Name (ZMod 3))

def normal (n : ℕ) (w : List (Syntax (Γ:=Γ) (Q:=Q))) : Part (List (Syntax (Γ:=Γ) (Q:=Q))) :=
  CommonCompiler.service A M (.inr ()) (terminalAlphabet A) (fun x => raw x.1 x.2) (n,w)

theorem partrec_normal : Partrec₂ (normal A M) :=
  CommonCompiler.partrec_service A M (.inr ()) (terminalAlphabet A) partrec_raw

def test : (i : Fin 3) → ℕ → List (Symbols (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) k i) →
    Part (Option (Keys (Γ:=Γ) (Q:=Q) k i))
  | 0 => fun _ => GroupFamily.test s
  | 1 => fun n => ProductFamily.test [.zero] (normal A M n)
  | 2 => fun n => EffectiveNames.Double.test e₁ e₂ Word.grade [.zero] (normal A M n)

def tables (n : ℕ) : ℕ → Part (List (List Sigma × List Sigma)) :=
  FamilyProgram.compute (r:=rel) (code (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k)) search
    none (fun i => test s A M e₁ e₂ i n)

theorem partrec_test (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))
    (i : Fin 3) : Partrec₂ (test s A M e₁ e₂ i) := by
  fin_cases i
  · exact (GroupFamily.partrec_test s h).comp Computable.snd
  · exact ProductFamily.partrec_test (A:=Syntax (Γ:=Γ) (Q:=Q)) [.zero] (partrec_normal A M)
  · exact EffectiveNames.Double.partrec_test (P₁:=P₁) (P₂:=P₂) (k₀:=ZMod 2) (n:=7)
      e₁ e₂ (Word.grade (S:=Sigma) (Γ:=Bool × Γ) (Q:=ParameterCode.Control Q)) [.zero]
      (partrec_normal A M)

theorem partrec_tables (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    Partrec₂ (tables s A M e₁ e₂) :=
  FamilyProgram.partrec_compute _ _ _
    (fun i => ThreeCodes.primrec_words i _ (primrec_cost i))
    (fun i => ThreeCodes.primrec_encode i _ (primrec_cost i)) primrec_shortlex
    (partrec_test s A M e₁ e₂ h)

theorem exists_fixed_point (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    ∃ n, raw n = tableNormal (tables s A M e₁ e₂ n) := by
  have hh := partrec_tableNormal_parameter (partrec_tables s A M e₁ e₂ h)
  have hc : Partrec₂ (fun c : Nat.Partrec.Code => tableNormal (tables s A M e₁ e₂ (Encodable.encode c))) :=
    hh.comp (Computable.encode.comp Computable.fst) Computable.snd
  obtain ⟨c,hc⟩ := WordProgramming.fixed_point hc
  exact ⟨Encodable.encode c, (raw_encode c).trans hc⟩

variable (decode : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a)
  (realizes : ∀ index, Word.Realizes (terminalAlphabet A) (terminalMachine A M index) (raw index))
  (he₁ : ∀ p, EffectiveNames.Enlargement.Coeff.value (e₁ p) *
    EffectiveNames.Enlargement.Coeff.value (e₁ p) = EffectiveNames.Enlargement.Coeff.value (e₁ p))
  (he₂ : ∀ p, EffectiveNames.Enlargement.Coeff.value (e₂ p) *
    EffectiveNames.Enlargement.Coeff.value (e₂ p) = EffectiveNames.Enlargement.Coeff.value (e₂ p))

include decode realizes he₁ he₂

omit [Finite P₁] [Finite P₂] in
theorem certificate (index n : ℕ) (budget : PartialBudget (raw index) (3 * (n / 10)))
    (i : Fin 3) : TestCertificate (code (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k) i)
      (test s A M e₁ e₂ i index) n := by
  let C := CommonCompiler.calculus A M (.inr ()) (terminalAlphabet A) index decode
    (f:=fun x => raw x.1 x.2) budget (realizes index)
  have hf (u : List (Syntax (Γ:=Γ) (Q:=Q)))
      (hu : C.grade (FreeMonoid.ofList u) ≤ n / 10) :
      (C.normal (FreeMonoid.ofList u)).toList ∈ normal A M index u := by
    apply CommonCompiler.service_full A M (.inr ()) (terminalAlphabet A) index
      decode budget (realizes index) u
    exact hu.trans (by omega)
  fin_cases i
  · exact GroupFamily.certificate s _ n
  · exact ProductFamily.certificate C _ (Path.letterGrade Word.gradeCell)
      (ProductFamily.grade_cost C _ (fun _ => rfl))
      (ThreeCodes.cost_padding _ _) (by omega) hf
  · exact ActionFamily.certificate
      (EffectiveNames.Double.interpretation (k₀:=ZMod 2) (n:=7) e₁ e₂ C he₁ he₂)
      _ (ThreeCodes.cost_padding _ _) le_rfl _
      (fun w hw => EffectiveNames.Double.test_full e₁ e₂ _ C he₁ he₂ w hw hf)

omit [Finite P₁] [Finite P₂] in
theorem all_budgets (index : ℕ)
    (fixed : raw index = tableNormal (tables s A M e₁ e₂ index)) :
    ∀ n, GoodTable (r:=rel) (tables s A M e₁ e₂ index) n ∧ PartialBudget (raw index) n := by
  apply FamilyProgram.bootstrap _ _ _ _ wf_rel (raw index) fixed
    (fun i => ThreeCodes.zero_avoids i _) (fun i j h => ThreeCodes.disjoint h _ _)
  intro n hn budget
  have hc := certificate s A M e₁ e₂ decode realizes he₁ he₂ index n budget
  exact ⟨fun i => (hc i).total, fun i => (hc i).nonzero,
    fun i => (hc i).contextual, fun i => (hc i).ideal⟩

theorem exists_total_fixed_point
    (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    ∃ index, raw index = tableNormal (tables s A M e₁ e₂ index) ∧
      ∀ n, GoodTable (r:=rel) (tables s A M e₁ e₂ index) n ∧ PartialBudget (raw index) n := by
  obtain ⟨index, hi⟩ := exists_fixed_point s A M e₁ e₂ h
  exact ⟨index,hi,all_budgets s A M e₁ e₂ decode realizes he₁ he₂ index hi⟩

end
end SimpleFInftyOvergroups.ContextualEncoding.Source

end OAI
