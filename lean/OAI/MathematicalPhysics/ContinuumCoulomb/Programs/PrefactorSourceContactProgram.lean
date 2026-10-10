import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PrefactorCalibrationProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceContactCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationMesh

namespace OAI

/-! Raw-source contact coordinates with precisely the amplification forced
by the unit-charge mesh. The calibration base is the thirtieth power of
the encoded source size, so its amplification is a cube. -/

namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ExactQuantumFactoring.BitStackProgram

def input (a : ℚ) (C s p h : ℕ) (d : BinaryHeisenberg) : CalibratedContactProgram.Input :=
  (SourceContactProgram.size d ^ h,
    ((CalibrationMesh.base (SourceContactProgram.size d),
      PrefactorCalibration.precision C (SourceContactProgram.size d ^ p)),
      (d.coordinate,((SourcePositiveProgram.normalized s d).2,
        ((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).map
          (PrefactorCalibration.adjustedWeight a)))))

noncomputable def value (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p h k A B : ℕ) (d : BinaryHeisenberg) : List (ℚ×ℚ) :=
  CalibratedContactProgram.value rho ε c k A B (input a C s p h d)

noncomputable opaque coefficientsProgram (a : ℚ) (s : ℕ) :
    Procedure binaryHeisenbergCodec.encode (listCode ratCode)
      (fun d => ((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).map
        (PrefactorCalibration.adjustedWeight a)) :=
  (Procedure.listMap 0 0 (PrefactorCalibration.weightProgram a)).comp
    (SourceContactProgram.coefficientsProgram s)

noncomputable opaque inputProgram (a : ℚ) (C s p h : ℕ) :
    Procedure binaryHeisenbergCodec.encode CalibratedContactProgram.inputCode (input a C s p h) :=
  (SourceContactProgram.powerProgram h).pair
    (((SourceContactProgram.powerProgram 30).pair
      ((PrefactorCalibration.precisionProgram C).comp (SourceContactProgram.powerProgram p))).pair
        (SourceContactProgram.coordinatesProgram.pair
          ((SourceContactProgram.signedBondsProgram s).pair (coefficientsProgram a s))))

noncomputable opaque program (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p h k A B : ℕ) : Procedure binaryHeisenbergCodec.encode
      (listCode ContactRationalGadget.pointCode) (value rho a C ε c s p h k A B) :=
  (CalibratedContactProgram.program rho ε c k A B).comp (inputProgram a C s p h)

noncomputable def certificate (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p h k A B : ℕ) : Turing.TM2ComputableInPolyTime binaryHeisenbergCodec.encode
      (listCode ContactRationalGadget.pointCode) (value rho a C ε c s p h k A B) :=
  (program rho a C ε c s p h k A B).toTM2

end ContinuumCoulomb.PrefactorSourceContactProgram

end OAI
