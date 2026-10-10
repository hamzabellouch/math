import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.AutomaticCalibrationNormalization
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! All edges share one fixed calibration program and one rational
spacing. Mapping that program over the edge coefficients retains a
polynomial running time in the complete encoded input. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibrationList
open ExactQuantumFactoring.BitStackProgram

abbrev Environment := ℕ × ℕ
abbrev Input := Environment × List ℚ

def environmentCode : Environment → List Bool := prodCode unaryCode unaryCode

def inputCode : Input → List Bool := prodCode environmentCode (listCode ratCode)

def value (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : List ℚ :=
  x.2.map (fun K => AutomaticCalibration.normalizedValue rho ε c k A B (x.1.1, (x.1.2, K)))

noncomputable opaque elementProgram (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure (prodCode environmentCode ratCode) ratCode
      (fun x => AutomaticCalibration.normalizedValue rho ε c k A B (x.1.1, (x.1.2, x.2))) := by
  let env := Procedure.first environmentCode ratCode
  let n := (Procedure.first unaryCode unaryCode).comp env
  let p := (Procedure.second unaryCode unaryCode).comp env
  let coefficient := Procedure.second environmentCode ratCode
  exact (AutomaticCalibration.normalizedProgram rho ε c k A B).comp
    (n.pair (p.pair coefficient))

noncomputable opaque program (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode (listCode ratCode) (value rho ε c k A B) :=
  Procedure.listMapWith (ea := environmentCode) (eb := ratCode) (ec := ratCode)
    (f := fun e K => AutomaticCalibration.normalizedValue rho ε c k A B (e.1, (e.2, K)))
      0 0 (elementProgram rho ε c k A B)

noncomputable def certificate (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode (listCode ratCode) (value rho ε c k A B) :=
  (program rho ε c k A B).toTM2

theorem value_near_one (rho : ℕ) {ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 < c)
    (k A B : ℕ) (x : Input) (hN : 0 < x.1.1) :
    ∀ q ∈ value rho ε c k A B x, q ∈ Set.Icc (1 - ε / 2) (1 + ε / 2) := by
  intro q hq
  obtain ⟨K, _, rfl⟩ := List.mem_map.mp hq
  exact AutomaticCalibration.normalizedValue_mem rho hε hc k A B _ hN

theorem value_length (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) :
    (value rho ε c k A B x).length = x.2.length := by simp [value]

end ContinuumCoulomb.AutomaticCalibrationList

end

end OAI
