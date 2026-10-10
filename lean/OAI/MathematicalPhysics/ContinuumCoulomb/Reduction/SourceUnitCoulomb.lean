import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceNuclearProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.AffinePhysicalOutput

namespace OAI

/-! Literal source-to-unit-Coulomb packaging. The physical nuclei and the
full affine threshold pair use the same calibrated sites, amplification,
mesh and exact rational slab dimensions. -/

namespace ContinuumCoulomb.SourceUnitCoulomb
open ExactQuantumFactoring.BitStackProgram

noncomputable def input (rho C : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ)
    (d : BinaryHeisenberg) : AffinePhysicalOutput.Input :=
  (SourceNuclearProgram.input rho C ε c s p h k A B r d,
    SourcePhysicalThreshold.input rho C ε c s p h k A B q d)

noncomputable def value (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ)
    (d : BinaryHeisenberg) : UnitCoulomb :=
  AffinePhysicalOutput.value rho U F K (input rho C ε c s p h k A B q r d)

noncomputable opaque inputProgram (rho C : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) :
    Procedure binaryHeisenbergCodec.encode AffinePhysicalOutput.inputCode
      (input rho C ε c s p h k A B q r) :=
  (SourceNuclearProgram.inputProgram rho C ε c s p h k A B r).pair
    (SourcePhysicalThreshold.inputProgram rho C ε c s p h k A B q)

noncomputable opaque program (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) :
    Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (value rho C U F K ε c s p h k A B q r) :=
  (AffinePhysicalOutput.program rho U F K).comp (inputProgram rho C ε c s p h k A B q r)

noncomputable def certificate (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) :
    Turing.TM2ComputableInPolyTime binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (value rho C U F K ε c s p h k A B q r) :=
  (program rho C U F K ε c s p h k A B q r).toTM2

theorem nuclei (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) (d : BinaryHeisenberg) :
    (value rho C U F K ε c s p h k A B q r d).nuclei =
      SourceNuclearProgram.nuclei rho C U F K ε c s p h k A B r d := rfl

theorem electrons (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) (d : BinaryHeisenberg) :
    (value rho C U F K ε c s p h k A B q r d).electrons =
      (SourcePositiveProgram.output s d).vertices := rfl

theorem lower (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) (d : BinaryHeisenberg) :
    (value rho C U F K ε c s p h k A B q r d).lower.value =
      (SourcePhysicalThreshold.value rho C ε c s p h k A B q d).1 :=
  NuclearCoordinateOutput.rational_value _

theorem upper (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ) (d : BinaryHeisenberg) :
    (value rho C U F K ε c s p h k A B q r d).upper.value =
      (SourcePhysicalThreshold.value rho C ε c s p h k A B q d).2 :=
  NuclearCoordinateOutput.rational_value _

theorem nuclei_length (rho C U F K : ℕ) (ε c : ℚ) (s p h k A B q r : ℕ)
    (d : BinaryHeisenberg) :
    (value rho C U F K ε c s p h k A B q r d).nuclei.length =
      8*((2*SourcePhysicalThreshold.horizontalRadius k d+1)^2*
        (2*SourcePhysicalThreshold.verticalRadius k d+1)) :=
  SourceNuclearProgram.nuclei_length rho C U F K ε c s p h k A B r d

theorem actual_threshold_error (rho C U F K : ℕ) (hrho : 0 < rho) (ε c : ℚ)
    (s p h k A B q r : ℕ) (d : BinaryHeisenberg) {m : ℕ}
    (u : Fin m → CoulombPairSum.Point) (hu : Function.Injective u)
    (hsites : SourceNuclearProgram.sites rho C ε c s p h k A B d = List.ofFn u) :
    let v := CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u
    |((value rho C U F K ε c s p h k A B q r d).lower.value:ℝ)-
      (AffinePhysicalThreshold.exactValue rho
        (SourcePhysicalThreshold.input rho C ε c s p h k A B q d) v).1| ≤
          1/(((SourceContactProgram.size d^q:ℕ):ℝ)+1) ∧
    |((value rho C U F K ε c s p h k A B q r d).upper.value:ℝ)-
      (AffinePhysicalThreshold.exactValue rho
        (SourcePhysicalThreshold.input rho C ε c s p h k A B q d) v).2| ≤
          1/(((SourceContactProgram.size d^q:ℕ):ℝ)+1) := by
  dsimp only
  rw [lower,upper]
  exact SourcePhysicalThreshold.actual_error rho C hrho ε c s p h k A B q d u hu hsites

theorem valid_of_nodes (rho C U F K : ℕ) (hrho : 0 < rho) (ε c : ℚ)
    (s p h k A B q r : ℕ) (d : BinaryHeisenberg)
    (hne : 0 < (SourcePositiveProgram.output s d).vertices)
    (hnodes : (TransformedGauss.nodes rho U F K
      ((SourceNuclearProgram.input rho C ε c s p h k A B r d).1,
        CenteredGaussLabels.labels (SourceNuclearProgram.input rho C ε c s p h k A B r d).2)).Nodup)
    (hgap : (1:ℚ) ≤ CenteredPhysicalThreshold.amplification rho (SourcePhysicalThreshold.mesh k d)*
      (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹)^2*
        ((SourcePositiveProgram.output s d).upper-(SourcePositiveProgram.output s d).lower)) :
    (value rho C U F K ε c s p h k A B q r d).Valid := by
  apply UnitCoulombProgram.valid_of_nodes rho U F K
    (SourceNuclearProgram.input rho C ε c s p h k A B r d,
      ((SourcePositiveProgram.output s d).vertices,SourcePhysicalThreshold.value rho C ε c s p h k A B q d))
    hrho (SourcePhysicalThreshold.mesh_positive k d) hne hnodes
  rw [SourcePhysicalThreshold.gap]
  exact hgap

end ContinuumCoulomb.SourceUnitCoulomb

end OAI
