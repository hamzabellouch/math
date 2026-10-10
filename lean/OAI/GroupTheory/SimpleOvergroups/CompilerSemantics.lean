import Mathlib
import OAI.Computability.FiniteCompiler.Quotients
import OAI.GroupTheory.SimpleOvergroups.CommonCompiler
import OAI.GroupTheory.SimpleOvergroups.ContractedNormalForms

namespace OAI


namespace SimpleFInftyOvergroups.CommonCompiler
noncomputable section
open FiniteAlgebraicEnvelopes Compiler MachineRealization
open SemanticEncoding
open scoped Classical Compiler.HeadCodec

variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  (p : S) (B : Simulator.Alphabet T (Bool × Γ)) (index : ℕ)

local instance compilerSemanticsSectorOrder :
    LinearOrder (Control.Sector T (Bool × Γ) (ParameterMachine.State Q index)) :=
  ParameterCode.finiteOrder index

abbrev Mon := Word.Presentation B (ParameterMachine.machine A M p index)

local instance compilerSemanticsMonoidWithZero : MonoidWithZero (Mon A M p B index) :=
  Word.monoidWithZero B (ParameterMachine.machine A M p index)

variable (decode : ∀ g a, B.output g = some a → g = B.input a)
  {f : ℕ × List T → Part (List T)}
  (budget : ∀ m, PartialBudget (fun w => f (index,w)) m)
  (realizes : Word.Realizes B (ParameterMachine.machine A M p index) (fun w => f (index,w)))

def evaluation : FreeMonoid (Letter T Γ Q) →* Mon A M p B index :=
  (PresentedMonoid.mk (Word.Rel B (ParameterMachine.machine A M p index))).comp
    (retractWord index)

omit [Fintype T] [Fintype Γ] [Fintype Q] [DecidableEq Q] [Primcodable Q] in
 theorem evaluation_surjective : Function.Surjective (evaluation A M p B index) := by
  intro h
  obtain ⟨w,hw⟩ := PresentedMonoid.surjective_mk h
  refine ⟨includeWord index w, ?_⟩
  simpa only [evaluation, MonoidHom.comp_apply, retract_include_word] using hw

omit [Fintype T] [Fintype Γ] [Fintype Q] [DecidableEq T] [DecidableEq Γ]
  [DecidableEq Q] [Primcodable Q] in
 theorem includeWord_injective : Function.Injective (includeWord (T:=T) (Γ:=Γ) (Q:=Q) index) :=
  Function.LeftInverse.injective (retract_include_word index)

def normal (w : FreeMonoid (Letter T Γ Q)) : FreeMonoid (Letter T Γ Q) :=
  (calculus A M p B index decode (budget 0) realizes).normal w

 theorem normal_at (m : ℕ) :
    (calculus A M p B index decode (budget m) realizes).normal = normal A M p B index decode budget realizes := rfl

 theorem evaluation_iff (u v : FreeMonoid (Letter T Γ Q)) :
    evaluation A M p B index u = evaluation A M p B index v ↔
      normal A M p B index decode budget realizes u = normal A M p B index decode budget realizes v := by
  change _ ↔ includeWord index _ = includeWord index _
  rw [(includeWord_injective (T:=T) (Γ:=Γ) (Q:=Q) index).eq_iff]
  change Word.present B (ParameterMachine.machine A M p index) (retractWord index u).toList =
    Word.present B (ParameterMachine.machine A M p index) (retractWord index v).toList ↔ _
  exact Word.present_eq_iff_normal B (ParameterMachine.machine A M p index) decode
    (fun m => (budget m).totalize) (fun m => realizes.computesAt _ _ (budget m)) _ _

 theorem normal_idempotent (w : FreeMonoid (Letter T Γ Q)) :
    normal A M p B index decode budget realizes (normal A M p B index decode budget realizes w) =
      normal A M p B index decode budget realizes w := by
  exact (calculus A M p B index decode (budget (Word.grade w.toList)) realizes).idempotent w le_rfl

def normalPresentation : NormalPresentation (FreeMonoid (Letter T Γ Q)) (Mon A M p B index) where
  q := evaluation A M p B index
  surjective := evaluation_surjective A M p B index
  normal := normal A M p B index decode budget realizes
  omega := FreeMonoid.ofList [.zero]
  zero := by
    change Word.present B (ParameterMachine.machine A M p index)
      [retractLetter index .zero] = Word.present B (ParameterMachine.machine A M p index) [.zero]
    rw [show retractLetter index (.zero : Letter T Γ Q) = .zero from retract_include index .zero]
  complete := evaluation_iff A M p B index decode budget realizes
  idempotent := normal_idempotent A M p B index decode budget realizes
  fixesZero := (calculus A M p B index decode (budget 0) realizes).normal_omega

 include decode budget realizes in
 theorem zero_ne_one : (0 : Mon A M p B index) ≠ 1 := by
  intro h
  let P := normalPresentation A M p B index decode budget realizes
  have he := (P.complete P.omega 1).mp (by rw [P.zero,map_one]; exact h)
  have hone : P.normal 1 = 1 :=
    (calculus A M p B index decode (budget 0) realizes).normal_one
  rw [P.fixesZero,hone] at he
  have he' := congrArg FreeMonoid.toList he
  change [.zero] = ([] : List (Letter T Γ Q)) at he'
  contradiction

 include decode budget realizes in
 theorem nontrivial : Nontrivial (Mon A M p B index) :=
  nontrivial_of_ne _ _ (zero_ne_one A M p B index decode budget realizes)

end
end SimpleFInftyOvergroups.CommonCompiler

end OAI
