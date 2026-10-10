import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathsGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingProgram

namespace OAI

/-! Literal polynomial coefficient program for both parities of a path gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathCode
open ExactQuantumFactoring.BitStackProgram QuantumRoutingCode

abbrev Input := Bool × (ℚ × ℚ)
def inputCode : Input → List Bool := prodCode Procedure.boolCode (prodCode ratCode ratCode)
noncomputable opaque evenProgram : Procedure inputCode Procedure.boolCode Prod.fst := Procedure.first _ _
noncomputable opaque tailProgram : Procedure inputCode (prodCode ratCode ratCode) Prod.snd := Procedure.second _ _
noncomputable opaque radiusProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp tailProgram
noncomputable opaque weightProgram : Procedure inputCode ratCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp tailProgram
noncomputable opaque spokeProgram : Procedure inputCode ratCode
    (fun x => if x.1 then -2*x.2.1*x.2.2 else 2*x.2.1*x.2.2) := by
  let p := twiceProductProgram radiusProgram weightProgram
  exact (Procedure.conditional evenProgram (Procedure.ratNeg.comp p) p).congrFun
    (by rintro ⟨b,r,j⟩; cases b <;> simp [neg_mul])
noncomputable opaque offsetProgram : Procedure inputCode ratCode
    (fun x => 3/4+3*x.2.2^2+3*x.2.1^2) := by
  let j := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair (squareProgram weightProgram))
  let r := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair (squareProgram radiusProgram))
  exact Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant inputCode ratCode (3/4)).pair j)).pair r)

def coefficients (x : Input) : Fin 4 → ℚ :=
  ![x.2.1^2,x.2.1,if x.1 then -2*x.2.1*x.2.2 else 2*x.2.1*x.2.2,
    3/4+3*x.2.2^2+3*x.2.1^2]

noncomputable opaque coefficientProgram (k : Fin 4) : Procedure inputCode ratCode (fun x => coefficients x k) := by
  by_cases h0 : k = 0
  · subst k
    exact (squareProgram radiusProgram).congrFun (by intro x; rfl)
  by_cases h1 : k = 1
  · subst k
    exact radiusProgram.congrFun (by intro x; rfl)
  by_cases h2 : k = 2
  · subst k
    exact spokeProgram.congrFun (by intro x; rfl)
  have h3 : k = 3 := by omega
  subst k
  exact offsetProgram.congrFun (by intro x; rfl)

noncomputable opaque coefficientListProgram : Procedure inputCode (listCode ratCode)
    (fun x => List.ofFn (coefficients x)) :=
  QuantumRawExchange.fixedListProgram inputCode ratCode 4 (fun k x => coefficients x k) coefficientProgram

noncomputable def coefficientListCertificate : Turing.TM2ComputableInPolyTime
    inputCode (listCode ratCode) (fun x => List.ofFn (coefficients x)) := coefficientListProgram.toTM2

theorem coefficients_spoke (x : Input) (a : Fin 2) :
    (coefficients x ⟨a.val+1,by omega⟩ : ℝ) = qmaPathAmplitude x.1 (x.2.1:ℝ) (x.2.2:ℝ) a := by
  rcases x with ⟨b,r,j⟩
  cases b <;> fin_cases a <;> simp [coefficients,qmaPathAmplitude]

theorem coefficients_offset (x : Input) :
    (coefficients x 3 : ℝ) = qmaPathOffset (x.2.2:ℝ)+3*(x.2.1:ℝ)^2 := by
  simp [coefficients,qmaPathOffset]

end ContinuumCoulomb.QuantumPathCode

end

end OAI
