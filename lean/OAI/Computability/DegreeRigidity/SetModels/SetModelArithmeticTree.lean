import OAI.Computability.DegreeRigidity.Computability.ArithmeticTreeDefinability
import OAI.Computability.DegreeRigidity.OrdinalCodes.OmegaModelArithmetic

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic BoundedSetTheory TransitiveNameModel SetModelReals SetModelSyntax
open OmegaModelCore SetModelFunctions
universe u
noncomputable section

theorem Test.nodeCode_mem {M : ZFSet.{u}} (C : Context M) (t : Test)
    (O : Oracles) (hO : ∀ i, O i ∈ reals M) (v : ℕ) : t.nodeCode O v ∈ reals M :=
  arithmetic_comprehension C (t.nodeCode_arith v) O hO _ (fun _ => Iff.rfl)

theorem Test.nodeCode_mem_iff (t : Test) (O : Oracles) (v : ℕ) (s : List ℕ) :
    natSet.{u} (Encodable.encode s) ∈ realSet (t.nodeCode O v) ↔ s ∈ t.tree O v := by
  simp only [nat_mem_realSet,Test.nodeCode,decodeNode_encode,decide_eq_true_eq]
  rfl

theorem Test.nodeCode_definition {M : ZFSet.{u}} (C : Context M) (t : Test) (v : ℕ) :
    ArithmeticDefinition M (fun O n => t.nodeCode O v n = true) :=
  arith_definition C (t.nodeCode_arith v)

theorem Test.omega_nodeCode {α : Type u} (S : OmegaData α)
    (hP : S.PairingAxiom) (hU : S.UnionAxiom) (hS : S.SeparationAxiom)
    (t : Test) (O : Oracles) (hO : ∀ i, ∃ a, S.RealCode a (O i)) (v : ℕ) :
    ∃ a, S.RealCode a (t.nodeCode O v) :=
  S.omega_arithmetic_comprehension hP hU hS (t.nodeCode_arith v) O hO _ (fun _ => Iff.rfl)

theorem Test.omega_nodeCode_correct {α : Type u} (S : OmegaData α)
    (hP : S.PairingAxiom) (hU : S.UnionAxiom) (hS : S.SeparationAxiom)
    (t : Test) (O : Oracles) (hO : ∀ i, ∃ a, S.RealCode a (O i)) (v : ℕ) :
    ∃ a, S.mem a (S.power S.omega) ∧
      ∀ s : List ℕ, S.mem (S.num (Encodable.encode s)) a ↔ s ∈ t.tree O v := by
  obtain ⟨a,ha⟩ := t.omega_nodeCode S hP hU hS O hO v
  refine ⟨a,ha.1,fun s => ?_⟩
  change S.mem (S.num (Encodable.encode s)) a ↔ t.accepts O v s
  simpa only [Test.nodeCode,decodeNode_encode,decide_eq_true_eq] using ha.2 (Encodable.encode s)

end
end TuringRigidity.ArithmeticTree

end OAI
