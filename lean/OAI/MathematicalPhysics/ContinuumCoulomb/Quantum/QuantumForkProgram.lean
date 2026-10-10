import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkBounds

namespace OAI

/-! Literal rational coefficient program for the degree-reducing fork. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkCode
open ExactQuantumFactoring.BitStackProgram QuantumRoutingCode

noncomputable opaque offsetProgram : Procedure tripleCode ratCode
    (fun x => 3/4+3*x.2.1^2+3*x.2.2^2) := by
  let j := Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair (squareProgram secondProgram))
  let k := Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair (squareProgram thirdProgram))
  exact Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant tripleCode ratCode (3/4)).pair j)).pair k)

def coefficients (x : Triple) : Fin 6 → ℚ :=
  ![x.1^2,x.1,2*x.1*x.2.1,2*x.1*x.2.2,2*x.2.1*x.2.2,
    3/4+3*x.2.1^2+3*x.2.2^2+3*x.1^2]

noncomputable opaque coefficientProgram (k : Fin 6) :
    Procedure tripleCode ratCode (fun x => coefficients x k) := by
  by_cases h0 : k = 0
  · subst k
    exact (squareProgram firstProgram).congrFun (by intro x; rfl)
  by_cases h1 : k = 1
  · subst k
    exact firstProgram.congrFun (by intro x; rfl)
  by_cases h2 : k = 2
  · subst k
    exact (twiceProductProgram firstProgram secondProgram).congrFun (by intro x; rfl)
  by_cases h3 : k = 3
  · subst k
    exact (twiceProductProgram firstProgram thirdProgram).congrFun (by intro x; rfl)
  by_cases h4 : k = 4
  · subst k
    exact (twiceProductProgram secondProgram thirdProgram).congrFun (by intro x; rfl)
  have h5 : k = 5 := by omega
  subst k
  exact (Procedure.ratAdd.comp (offsetProgram.pair
      (Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair
        (squareProgram firstProgram))))).congrFun (by intro x; rfl)

noncomputable opaque coefficientListProgram : Procedure tripleCode (listCode ratCode)
    (fun x => List.ofFn (coefficients x)) :=
  QuantumRawExchange.fixedListProgram tripleCode ratCode 6 (fun k x => coefficients x k) coefficientProgram

noncomputable def coefficientListCertificate : Turing.TM2ComputableInPolyTime
    tripleCode (listCode ratCode) (fun x => List.ofFn (coefficients x)) := coefficientListProgram.toTM2

theorem coefficients_spoke (x : Triple) (a : Fin 3) :
    (coefficients x ⟨a.val+1,by omega⟩ : ℝ) =
      qmaForkAmplitude (x.1:ℝ) (x.2.1:ℝ) (x.2.2:ℝ) a := by
  fin_cases a <;> simp [coefficients,qmaForkAmplitude]

theorem coefficients_correction (x : Triple) :
    (coefficients x 4 : ℝ) = 2*(x.2.1:ℝ)*(x.2.2:ℝ) := by
  simp [coefficients]

theorem coefficients_offset (x : Triple) :
    (coefficients x 5 : ℝ) = qmaForkOffset (x.2.1:ℝ) (x.2.2:ℝ)+3*(x.1:ℝ)^2 := by
  simp [coefficients,qmaForkOffset]

end ContinuumCoulomb.QuantumForkCode

end

end OAI
