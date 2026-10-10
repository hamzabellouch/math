import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.AffinePhysicalThresholdProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.UnitCoulombProgram

namespace OAI

/-! A canonical unit-charge instance with the complete physical scalar offset.
The coordinate and threshold metadata remain explicit until the source program
supplies the same fixed polynomial scales to both components. -/

namespace ContinuumCoulomb.AffinePhysicalOutput
open ExactQuantumFactoring.BitStackProgram

abbrev Input := PhysicalNuclearProgram.Input × AffinePhysicalThreshold.Input

def inputCode : Input → List Bool :=
  prodCode PhysicalNuclearProgram.inputCode AffinePhysicalThreshold.inputCode

noncomputable def argument (rho : ℕ) (x : Input) : UnitCoulombProgram.Input :=
  (x.1,(x.2.1.2.1,AffinePhysicalThreshold.value rho x.2))

noncomputable def value (rho U C K : ℕ) (x : Input) : UnitCoulomb :=
  UnitCoulombProgram.value rho U C K (argument rho x)

noncomputable opaque argumentProgram (rho : ℕ) :
    Procedure inputCode UnitCoulombProgram.inputCode (argument rho) := by
  let geom := Procedure.first PhysicalNuclearProgram.inputCode AffinePhysicalThreshold.inputCode
  let numbers := Procedure.second PhysicalNuclearProgram.inputCode AffinePhysicalThreshold.inputCode
  let count := AffinePhysicalThreshold.electronsProgram.comp numbers
  let endpoints := (AffinePhysicalThreshold.program rho).comp numbers
  exact geom.pair (count.pair endpoints)

noncomputable opaque program (rho U C K : ℕ) :
    Procedure inputCode unitCoulombCodec.encode (value rho U C K) :=
  (UnitCoulombProgram.program rho U C K).comp (argumentProgram rho)

noncomputable def certificate (rho U C K : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode unitCoulombCodec.encode (value rho U C K) :=
  (program rho U C K).toTM2

theorem nuclei (rho U C K : ℕ) (x : Input) :
    (value rho U C K x).nuclei = PhysicalNuclearProgram.nuclei rho U C K x.1 := rfl

theorem electrons (rho U C K : ℕ) (x : Input) :
    (value rho U C K x).electrons = x.2.1.2.1 := rfl

theorem lower (rho U C K : ℕ) (x : Input) :
    (value rho U C K x).lower.value = (AffinePhysicalThreshold.value rho x.2).1 :=
  NuclearCoordinateOutput.rational_value _

theorem upper (rho U C K : ℕ) (x : Input) :
    (value rho U C K x).upper.value = (AffinePhysicalThreshold.value rho x.2).2 :=
  NuclearCoordinateOutput.rational_value _

theorem actual_error (rho U C K : ℕ) (hrho : 0 < rho) (x : Input)
    (hmesh : 0 < x.2.1.1.1) {m : ℕ}
    (u : Fin m → CoulombPairSum.Point) (hu : Function.Injective u)
    (hsites : x.2.2.2.1 = List.ofFn u) :
    let v := CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u
    |((value rho U C K x).lower.value:ℝ)-
      (AffinePhysicalThreshold.exactValue rho x.2 v).1| ≤ 1/(x.2.1.2.2.1+1:ℝ) ∧
    |((value rho U C K x).upper.value:ℝ)-
      (AffinePhysicalThreshold.exactValue rho x.2 v).2| ≤ 1/(x.2.1.2.2.1+1:ℝ) := by
  dsimp only
  rw [lower,upper]
  exact AffinePhysicalThreshold.actual_error rho hrho x.2 hmesh u hu hsites

theorem valid (rho U C K : ℕ) (x : Input) (hne : 0 < x.2.1.2.1)
    (hpositions : ((PhysicalNuclearProgram.nuclei rho U C K x.1).map BinaryPosition.value).Nodup)
    (hgap : (1:ℚ) ≤ CenteredPhysicalThreshold.amplification rho x.2.1.1.1*x.2.2.1^2*
      (x.2.1.2.2.2.2-x.2.1.2.2.2.1)) : (value rho U C K x).Valid := by
  apply UnitCoulombProgram.valid rho U C K (x.1,(x.2.1.2.1,AffinePhysicalThreshold.value rho x.2))
    hne hpositions
  rw [AffinePhysicalThreshold.gap]
  exact hgap

end ContinuumCoulomb.AffinePhysicalOutput

end OAI
