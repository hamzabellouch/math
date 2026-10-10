import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.AffinePhysicalThresholdProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PrefactorSourceContactProgram

namespace OAI

/-! Literal raw-source assembly of the complete physical threshold pair.
The same fixed powers determine the calibration amplification, the centered
nuclear mesh, and the rational slab dimensions. -/

namespace ContinuumCoulomb.SourcePhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

def mesh (k : ℕ) (d : BinaryHeisenberg) : ℕ := SourceContactProgram.size d^(10*k)
def horizontalRadius (k : ℕ) (d : BinaryHeisenberg) : ℕ := SourceContactProgram.size d^(60*k)
def verticalRadius (k : ℕ) (d : BinaryHeisenberg) : ℕ := SourceContactProgram.size d^(15*k)
def slabHorizontal (k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  SlabBoxSchedule.centeredWidth (horizontalRadius k d) (mesh k d)
def slabVertical (k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  SlabBoxSchedule.centeredWidth (verticalRadius k d) (mesh k d)

theorem horizontal_product (k : ℕ) (d : BinaryHeisenberg) :
    horizontalRadius k d = SourceContactProgram.size d^(50*k)*mesh k d := by
  dsimp [horizontalRadius,mesh]
  rw [← pow_add]
  congr 1
  omega

theorem vertical_product (k : ℕ) (d : BinaryHeisenberg) :
    verticalRadius k d = SourceContactProgram.size d^(5*k)*mesh k d := by
  dsimp [verticalRadius,mesh]
  rw [← pow_add]
  congr 1
  omega

theorem mesh_positive (k : ℕ) (d : BinaryHeisenberg) : 0 < mesh k d := by
  apply pow_pos
  exact lt_of_lt_of_le (by decide : 0 < 2) (SourceContactProgram.size_ge_two d)

theorem slabHorizontal_bounds (k : ℕ) (d : BinaryHeisenberg) :
    ((SourceContactProgram.size d^(50*k):ℕ):ℚ) ≤ slabHorizontal k d ∧
      slabHorizontal k d ≤ 2*((SourceContactProgram.size d^(50*k):ℕ):ℚ) := by
  rw [slabHorizontal,horizontal_product]
  exact SlabBoxSchedule.centeredWidth_product_bounds _ _
    (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (SourceContactProgram.size_ge_two d)) _)
    (mesh_positive k d)

theorem slabVertical_bounds (k : ℕ) (d : BinaryHeisenberg) :
    ((SourceContactProgram.size d^(5*k):ℕ):ℚ) ≤ slabVertical k d ∧
      slabVertical k d ≤ 2*((SourceContactProgram.size d^(5*k):ℕ):ℚ) := by
  rw [slabVertical,vertical_product]
  exact SlabBoxSchedule.centeredWidth_product_bounds _ _
    (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (SourceContactProgram.size_ge_two d)) _)
    (mesh_positive k d)

noncomputable def input (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) : AffinePhysicalThreshold.Input :=
  (((mesh k d,
        (horizontalRadius k d,verticalRadius k d)),
      ((SourcePositiveProgram.output s d).vertices,
        (SourceContactProgram.size d^q,
          ((SourcePositiveProgram.output s d).lower,(SourcePositiveProgram.output s d).upper)))),
    (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹,
      (PrefactorSourceContactProgram.value rho (CalibrationMesh.prefactor rho) C ε c
        s p h k A B d,
       (SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2))))

noncomputable def value (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) : ℚ×ℚ :=
  AffinePhysicalThreshold.value rho (input rho C ε c s p h k A B q d)

noncomputable opaque tauProgram (B : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹)) :=
  Procedure.ratInv.comp (Procedure.natToRat.comp
    (Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (30*B))))

noncomputable opaque inputProgram (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ) :
    Procedure binaryHeisenbergCodec.encode AffinePhysicalThreshold.inputCode
      (input rho C ε c s p h k A B q) := by
  let geometry := (SourceContactProgram.powerProgram (10*k)).pair
    ((SourceContactProgram.powerProgram (60*k)).pair (SourceContactProgram.powerProgram (15*k)))
  let bounds := (SourcePositiveProgram.lowerProgram s).pair (SourcePositiveProgram.upperProgram s)
  let metadata := (SourcePositiveProgram.verticesProgram s).pair
    ((SourceContactProgram.powerProgram q).pair bounds)
  let sites := PrefactorSourceContactProgram.program rho (CalibrationMesh.prefactor rho) C ε c
    s p h k A B
  let weights := SourceContactProgram.coefficientsProgram s
  exact (geometry.pair metadata).pair ((tauProgram B).pair (sites.pair weights))

noncomputable opaque program (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ) :
    Procedure binaryHeisenbergCodec.encode (prodCode ratCode ratCode)
      (value rho C ε c s p h k A B q) :=
  (AffinePhysicalThreshold.program rho).comp (inputProgram rho C ε c s p h k A B q)

noncomputable def certificate (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ) :
    Turing.TM2ComputableInPolyTime binaryHeisenbergCodec.encode (prodCode ratCode ratCode)
      (value rho C ε c s p h k A B q) := (program rho C ε c s p h k A B q).toTM2

theorem actual_error (rho C : ℕ) (hrho : 0 < rho) (ε c : ℚ)
    (s p h k A B q : ℕ) (d : BinaryHeisenberg) {m : ℕ}
    (u : Fin m → CoulombPairSum.Point) (hu : Function.Injective u)
    (hsites : PrefactorSourceContactProgram.value rho (CalibrationMesh.prefactor rho)
      C ε c s p h k A B d = List.ofFn u) :
    let v := CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u
    |((value rho C ε c s p h k A B q d).1:ℝ)-
      (AffinePhysicalThreshold.exactValue rho (input rho C ε c s p h k A B q d) v).1| ≤
        1/(((SourceContactProgram.size d^q:ℕ):ℝ)+1) ∧
    |((value rho C ε c s p h k A B q d).2:ℝ)-
      (AffinePhysicalThreshold.exactValue rho (input rho C ε c s p h k A B q d) v).2| ≤
        1/(((SourceContactProgram.size d^q:ℕ):ℝ)+1) := by
  exact AffinePhysicalThreshold.actual_error rho hrho (input rho C ε c s p h k A B q d)
    (mesh_positive k d) u hu hsites

theorem gap (rho C : ℕ) (ε c : ℚ) (s p h k A B q : ℕ) (d : BinaryHeisenberg) :
    (value rho C ε c s p h k A B q d).2-(value rho C ε c s p h k A B q d).1 =
      CenteredPhysicalThreshold.amplification rho (SourceContactProgram.size d^(10*k))*
        (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹)^2*
          ((SourcePositiveProgram.output s d).upper-(SourcePositiveProgram.output s d).lower) := by
  exact AffinePhysicalThreshold.gap rho (input rho C ε c s p h k A B q d)

end ContinuumCoulomb.SourcePhysicalThreshold

end OAI
