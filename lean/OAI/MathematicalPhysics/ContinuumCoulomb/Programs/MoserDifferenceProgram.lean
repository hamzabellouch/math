import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserDifferenceBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PiProgram

namespace OAI

/-! Literal polynomial integer arithmetic for the fixed finite-difference
precision and rational step of the manufactured field evaluator. -/

namespace ContinuumCoulomb.MoserDifferenceBudget
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque nextSquareProgram : Procedure unaryCode unaryCode (fun P => (P+1)^2) :=
  (Procedure.unaryMul.comp (Procedure.unarySuccessor.pair Procedure.unarySuccessor)).congrFun
    (by intro P; simp only [pow_two]; rfl)

noncomputable opaque nextCubeProgram : Procedure unaryCode unaryCode (fun P => (P+1)^3) :=
  (Procedure.unaryMul.comp (nextSquareProgram.pair Procedure.unarySuccessor)).congrFun
    (by intro P; simp only [pow_succ]; rfl)

/-- A fixed integer bounds the finite-difference precision independently of the
input instance. -/
noncomputable opaque precisionScaleData : {n : ℕ // n = 16384*guard^2} := ⟨16384*guard^2,rfl⟩
noncomputable def precisionScale : ℕ := precisionScaleData.val

theorem precisionScale_eq : precisionScale = 16384*guard^2 := precisionScaleData.property

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision := by
  let p := Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode precisionScale).pair nextCubeProgram)
  exact p.congrFun (by
    intro P
    change precisionScale*(P+1)^3 = precision P
    rw [precisionScale_eq]
    rfl)

noncomputable opaque stepDenominatorProgram : Procedure unaryCode ratCode
    (fun P => 16*(guard:ℚ)*(P+1)) := by
  let c := Procedure.constant unaryCode ratCode (16*(guard:ℚ))
  let p := Procedure.natToRat.comp (Procedure.unaryToBits.comp Procedure.unarySuccessor)
  exact (Procedure.ratMul.comp (c.pair p)).congrFun (by intro P; change 16*(guard:ℚ)*(Nat.succ P:ℚ) = _; simp only [Nat.cast_succ])

noncomputable opaque stepProgram : Procedure unaryCode ratCode step :=
  Procedure.ratInv.comp stepDenominatorProgram

end ContinuumCoulomb.MoserDifferenceBudget

end OAI
