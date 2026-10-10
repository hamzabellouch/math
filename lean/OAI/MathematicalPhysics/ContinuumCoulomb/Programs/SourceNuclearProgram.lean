import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePhysicalThreshold
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PhysicalNuclearProgram

namespace OAI

/-! Raw-source assembly of the actual transported unit nuclei. The well
scale is exactly lambda, the cutoff width is the exact centered slab width,
and all three lattice radii come from the same powers as the thresholds. -/

namespace ContinuumCoulomb.SourceNuclearProgram
open ExactQuantumFactoring.BitStackProgram

noncomputable def sites (rho C : ℕ) (ε c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) : List (ℚ×ℚ) :=
  PrefactorSourceContactProgram.value rho (CalibrationMesh.prefactor rho) C ε c s p h k A B d

def amplification (rho k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  CenteredPhysicalThreshold.amplification rho (SourcePhysicalThreshold.mesh k d)

noncomputable def input (rho C : ℕ) (ε c : ℚ) (s p h k A B r : ℕ)
    (d : BinaryHeisenberg) : PhysicalNuclearProgram.Input :=
  (((SourceContactProgram.size d^r,SourcePhysicalThreshold.mesh k d),
    ((amplification rho k d,SourcePhysicalThreshold.slabVertical k d),
      sites rho C ε c s p h k A B d)),
    (SourcePhysicalThreshold.horizontalRadius k d,
      (SourcePhysicalThreshold.horizontalRadius k d,SourcePhysicalThreshold.verticalRadius k d)))

noncomputable def nuclei (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B r : ℕ)
    (d : BinaryHeisenberg) : List BinaryPosition :=
  PhysicalNuclearProgram.nuclei rho U F K (input rho C ε c s p h k A B r d)

noncomputable opaque amplificationProgram (rho k : ℕ) :
    Procedure binaryHeisenbergCodec.encode ratCode (amplification rho k) := by
  let n := Procedure.natToRat.comp
    (Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (10*k)))
  let n2 := Procedure.ratMul.comp (n.pair n)
  let n3 := Procedure.ratMul.comp (n2.pair n)
  let num := Procedure.ratMul.comp
    ((Procedure.constant binaryHeisenbergCodec.encode ratCode 8).pair n3)
  exact (Procedure.ratDiv.comp (num.pair
    (Procedure.constant binaryHeisenbergCodec.encode ratCode (rho:ℚ)))).congrFun (by
      intro d
      change (8*((((SourceContactProgram.size d^(10*k):ℕ):ℚ)*
          ((SourceContactProgram.size d^(10*k):ℕ):ℚ))*
          ((SourceContactProgram.size d^(10*k):ℕ):ℚ)))/(rho:ℚ) = _
      simp only [amplification,CenteredPhysicalThreshold.amplification,SourcePhysicalThreshold.mesh]
      ring)

noncomputable opaque verticalProgram (k : ℕ) :
    Procedure binaryHeisenbergCodec.encode ratCode (SourcePhysicalThreshold.slabVertical k) := by
  let m := Procedure.natToRat.comp
    (Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (10*k)))
  let s := Procedure.natToRat.comp
    (Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (15*k)))
  let num := Procedure.ratAdd.comp
    (s.pair (Procedure.constant binaryHeisenbergCodec.encode ratCode (1/2:ℚ)))
  exact (Procedure.ratDiv.comp (num.pair m)).congrFun (by intro d; rfl)

noncomputable opaque inputProgram (rho C : ℕ) (ε c : ℚ) (s p h k A B r : ℕ) :
    Procedure binaryHeisenbergCodec.encode PhysicalNuclearProgram.inputCode
      (input rho C ε c s p h k A B r) := by
  let mesh := Procedure.unaryToBits.comp (SourceContactProgram.powerProgram (10*k))
  let precise := SourceContactProgram.powerProgram r
  let hs := SourceContactProgram.powerProgram (60*k)
  let vs := SourceContactProgram.powerProgram (15*k)
  let points := PrefactorSourceContactProgram.program rho (CalibrationMesh.prefactor rho) C ε c
    s p h k A B
  let field := ((amplificationProgram rho k).pair (verticalProgram k)).pair points
  exact ((precise.pair mesh).pair field).pair (hs.pair (hs.pair vs))

noncomputable opaque program (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B r : ℕ) :
    Procedure binaryHeisenbergCodec.encode (BinaryEncoding.list binaryPositionCodec).encode
      (nuclei rho C U F K ε c s p h k A B r) :=
  (PhysicalNuclearProgram.program rho U F K).comp (inputProgram rho C ε c s p h k A B r)

noncomputable def certificate (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B r : ℕ) :
    Turing.TM2ComputableInPolyTime binaryHeisenbergCodec.encode
      (BinaryEncoding.list binaryPositionCodec).encode (nuclei rho C U F K ε c s p h k A B r) :=
  (program rho C U F K ε c s p h k A B r).toTM2

theorem mesh (rho C : ℕ) (ε c : ℚ) (s p h k A B r : ℕ) (d : BinaryHeisenberg) :
    (input rho C ε c s p h k A B r d).1.1.2 = SourcePhysicalThreshold.mesh k d := rfl

theorem field_scale (rho C : ℕ) (ε c : ℚ) (s p h k A B r : ℕ) (d : BinaryHeisenberg) :
    (input rho C ε c s p h k A B r d).1.2.1.1 = amplification rho k d := rfl

theorem field_width (rho C : ℕ) (ε c : ℚ) (s p h k A B r : ℕ) (d : BinaryHeisenberg) :
    (input rho C ε c s p h k A B r d).1.2.1.2 = SourcePhysicalThreshold.slabVertical k d := rfl

theorem field_sites (rho C : ℕ) (ε c : ℚ) (s p h k A B r : ℕ) (d : BinaryHeisenberg) :
    (input rho C ε c s p h k A B r d).1.2.2 = sites rho C ε c s p h k A B d := rfl

theorem real_positions (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B r : ℕ)
    (d : BinaryHeisenberg) :
    (nuclei rho C U F K ε c s p h k A B r d).map (fun a => realPosition a.value) =
      (TransformedGauss.nodes rho U F K
        ((input rho C ε c s p h k A B r d).1,
          CenteredGaussLabels.labels (input rho C ε c s p h k A B r d).2)).map
        (fun a => (PhysicalNuclearProgram.factor rho (SourcePhysicalThreshold.mesh k d):ℝ) •
          CappedKernelProgram.position a) := by
  simp only [nuclei,PhysicalNuclearProgram.nuclei,PhysicalNuclearProgram.triples,
    NuclearCoordinateOutput.positions,List.map_map,Function.comp_def,
    NuclearCoordinateOutput.real_position,PhysicalNuclearProgram.scale_position]
  rfl

theorem nuclei_length (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B r : ℕ)
    (d : BinaryHeisenberg) :
    (nuclei rho C U F K ε c s p h k A B r d).length =
      8*((2*SourcePhysicalThreshold.horizontalRadius k d+1)^2*
        (2*SourcePhysicalThreshold.verticalRadius k d+1)) := by
  rw [nuclei,PhysicalNuclearProgram.nuclei_length]
  dsimp only [input]
  ring

end ContinuumCoulomb.SourceNuclearProgram

end OAI
