import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CalibratedContactProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourcePositiveProgram

namespace OAI

/-! Literal composition from the encoded source to the calibrated
contact coordinates. The signed retained bonds determine the geometric
strips; the final positive bond list supplies their nineteen target weights. -/

namespace ContinuumCoulomb.SourceContactProgram
open ExactQuantumFactoring.BitStackProgram

def size (d : BinaryHeisenberg) : ℕ := SourceMetadataProgram.size d + 1

def input (s p h : ℕ) (d : BinaryHeisenberg) : CalibratedContactProgram.Input :=
  (size d ^ h, ((size d, size d ^ p), (d.coordinate,
    ((SourcePositiveProgram.normalized s d).2,
      (SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)))))

noncomputable def value (rho : ℕ) (ε c : ℚ) (s p h k A B : ℕ) (d : BinaryHeisenberg) :
    List (ℚ × ℚ) :=
  CalibratedContactProgram.value rho ε c k A B (input s p h d)

noncomputable opaque coordinateProgram : Procedure SourcePrograms.coordinateCodec.encode
    ContactCanonicalEdgeProgram.latticeCode id := by
  let parsed := SourcePrograms.pairInput BinaryEncoding.integer BinaryEncoding.integer
    PrefixPrograms.integer
  exact ((EncodingPrograms.integerInput.comp ((Procedure.first _ _).comp parsed)).pair
    (EncodingPrograms.integerInput.comp ((Procedure.second _ _).comp parsed))).result
      (by intro x; rfl)

noncomputable opaque coordinatesProgram : Procedure binaryHeisenbergCodec.encode
    (listCode ContactCanonicalEdgeProgram.latticeCode) BinaryHeisenberg.coordinate :=
  ((Procedure.listMap (0,0) (0,0) coordinateProgram).comp SourcePrograms.coordinates).result
    (by intro d; simp only [Function.comp_apply,List.map_id])

noncomputable opaque sizeProgram : Procedure binaryHeisenbergCodec.encode unaryCode size :=
  Procedure.unarySuccessor.comp SourceMetadataProgram.sizeProgram

noncomputable def powerProgram : (p : ℕ) → Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => size d ^ p)
  | 0 => Procedure.constant _ unaryCode 1
  | p+1 => (Procedure.unaryMul.comp ((powerProgram p).pair sizeProgram)).congrFun
      (by intro d; exact (pow_succ (size d) p).symm)

noncomputable opaque signedBondsProgram (s : ℕ) : Procedure binaryHeisenbergCodec.encode
    (listCode MediatorListProgram.bondCode) (fun d => (SourcePositiveProgram.normalized s d).2) :=
  (Procedure.second _ _).comp (SourcePositiveProgram.normalizedProgram s)

noncomputable opaque coefficientProgram : Procedure MediatorListProgram.bondCode ratCode
    (fun e => e.2.2) := (Procedure.second _ _).comp (Procedure.second _ _)

noncomputable opaque coefficientsProgram (s : ℕ) : Procedure binaryHeisenbergCodec.encode
    (listCode ratCode) (fun d => (SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)) :=
  (Procedure.listMap MediatorListProgram.zeroBond 0 coefficientProgram).comp
    (SourcePositiveProgram.bondsProgram s)

noncomputable opaque inputProgram (s p h : ℕ) : Procedure binaryHeisenbergCodec.encode
    CalibratedContactProgram.inputCode (input s p h) :=
  (powerProgram h).pair ((sizeProgram.pair (powerProgram p)).pair
    (coordinatesProgram.pair ((signedBondsProgram s).pair (coefficientsProgram s))))

noncomputable opaque program (rho : ℕ) (ε c : ℚ) (s p h k A B : ℕ) :
    Procedure binaryHeisenbergCodec.encode (listCode ContactRationalGadget.pointCode)
      (value rho ε c s p h k A B) :=
  (CalibratedContactProgram.program rho ε c k A B).comp (inputProgram s p h)

noncomputable def certificate (rho : ℕ) (ε c : ℚ) (s p h k A B : ℕ) :
    Turing.TM2ComputableInPolyTime binaryHeisenbergCodec.encode
      (listCode ContactRationalGadget.pointCode) (value rho ε c s p h k A B) :=
  (program rho ε c s p h k A B).toTM2

theorem size_ge_two (d : BinaryHeisenberg) : 2 ≤ size d := by
  simp only [size,SourceMetadataProgram.size]
  omega

end ContinuumCoulomb.SourceContactProgram

end OAI
