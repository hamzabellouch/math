import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PhysicalThresholdProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.UnitCoulombProgram

namespace OAI

/-! Composition of the actual physical-nucleus generator with the computed
slab/reference threshold shift, using the continuum promise's canonical codec. -/

namespace ContinuumCoulomb.PhysicalThresholdOutput
open ExactQuantumFactoring.BitStackProgram

abbrev Input := PhysicalNuclearProgram.Input × PhysicalThreshold.Input

def inputCode : Input → List Bool :=
  prodCode PhysicalNuclearProgram.inputCode PhysicalThreshold.inputCode

def argument (rho : ℕ) (x : Input) : UnitCoulombProgram.Input :=
  (x.1,(x.2.2.1,PhysicalThreshold.value rho x.2))

noncomputable def value (rho U C K : ℕ) (x : Input) : UnitCoulomb :=
  UnitCoulombProgram.value rho U C K (argument rho x)

noncomputable opaque argumentProgram (rho : ℕ) :
    Procedure inputCode UnitCoulombProgram.inputCode (argument rho) := by
  let geom := Procedure.first PhysicalNuclearProgram.inputCode PhysicalThreshold.inputCode
  let numbers := Procedure.second PhysicalNuclearProgram.inputCode PhysicalThreshold.inputCode
  let count := PhysicalThreshold.electronsProgram.comp numbers
  let endpoints := (PhysicalThreshold.program rho).comp numbers
  exact geom.pair (count.pair endpoints)

noncomputable opaque program (rho U C K : ℕ) :
    Procedure inputCode unitCoulombCodec.encode (value rho U C K) :=
  (UnitCoulombProgram.program rho U C K).comp (argumentProgram rho)

noncomputable def certificate (rho U C K : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode unitCoulombCodec.encode (value rho U C K) :=
  (program rho U C K).toTM2

theorem electrons (rho U C K : ℕ) (x : Input) :
    (value rho U C K x).electrons = x.2.2.1 := rfl

theorem nuclei (rho U C K : ℕ) (x : Input) :
    (value rho U C K x).nuclei = PhysicalNuclearProgram.nuclei rho U C K x.1 := rfl

theorem lower (rho U C K : ℕ) (x : Input) :
    (value rho U C K x).lower.value = (PhysicalThreshold.value rho x.2).1 :=
  NuclearCoordinateOutput.rational_value _

theorem upper (rho U C K : ℕ) (x : Input) :
    (value rho U C K x).upper.value = (PhysicalThreshold.value rho x.2).2 :=
  NuclearCoordinateOutput.rational_value _

theorem valid (rho U C K : ℕ) (x : Input) (hne : 0 < x.2.2.1)
    (hpositions : ((PhysicalNuclearProgram.nuclei rho U C K x.1).map BinaryPosition.value).Nodup)
    (hgap : (1:ℚ) ≤ PhysicalThreshold.amplification rho x.2.1.1*
      (x.2.2.2.2.2-x.2.2.2.2.1)) : (value rho U C K x).Valid := by
  apply UnitCoulombProgram.valid rho U C K (argument rho x) hne hpositions
  change (1:ℚ) ≤ (PhysicalThreshold.value rho x.2).2-(PhysicalThreshold.value rho x.2).1
  rw [PhysicalThreshold.gap]
  exact hgap

end ContinuumCoulomb.PhysicalThresholdOutput

end OAI
