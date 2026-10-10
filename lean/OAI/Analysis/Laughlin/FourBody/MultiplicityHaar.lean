import OAI.Analysis.Laughlin.FourBody.RetainedInclusions
import OAI.Analysis.Laughlin.Spin.HaarOrthogonality
import OAI.Analysis.Laughlin.Spin.Sandwich

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem retainedFourInclusion_adjoint_SU2 (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (g : SourceSU2) :
    (retainedFourInclusion Q D hQ r)ᴴ * fourBodySpinRepresentation Q g =
      sourceSpinRepresentation (fourSpinWeight Q D) g * (retainedFourInclusion Q D hQ r)ᴴ := by
  have h := congrArg Matrix.conjTranspose (retainedFourInclusion_SU2 Q D hQ r g⁻¹)
  simpa only [Matrix.conjTranspose_mul,fourBodySpinRepresentation_inv,sourceSpinRepresentation_inv,
    Matrix.conjTranspose_conjTranspose] using h

theorem fourBody_haar_compressed (Q D E : ℕ) (hD : D+2 ≤ Q) (hE : E+2 ≤ Q)
    (r : OddPairLabel D) (s : OddPairLabel E) (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s =
    rectangularIntegral sourceHaar (rectangularOrbit
      (sourceSpinRepresentation (fourSpinWeight Q D)) (sourceSpinRepresentation (fourSpinWeight Q E))
      ((retainedFourInclusion Q D hD r)ᴴ * M * retainedFourInclusion Q E hE s)) := by
  change (retainedFourInclusion Q D hD r)ᴴ * entrywiseIntegral sourceHaar
    (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s = _
  rw [← integral_matrix_sandwich sourceHaar _
    (compact_conjugateOrbit_integrable sourceHaar _ (fourBodySpinRepresentation_continuous Q) M)]
  funext i j
  apply integral_congr_ae
  filter_upwards [] with g
  have hs := retainedFourInclusion_SU2 Q E hE s g⁻¹
  simp only [conjugateOrbit,rectangularOrbit]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,retainedFourInclusion_adjoint_SU2,
    Matrix.mul_assoc,Matrix.mul_assoc,hs]
  simp only [Matrix.mul_assoc]

theorem fourBody_haar_multiplicity_block (Q D : ℕ) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q D hD s =
      (Matrix.trace ((retainedFourInclusion Q D hD r)ᴴ*M*retainedFourInclusion Q D hD s) /
        (4*Q-1-2*D : ℕ)) • 1 := by
  rw [fourBody_haar_compressed,source_equal_spin_haar_trace]
  have hd : ((fourSpinWeight Q D+1 : ℕ) : ℂ) = ((4*Q-1-2*D : ℕ) : ℂ) := by
    exact_mod_cast fourSpinWeight_dimension Q D hD
  rw [hd]

theorem fourBody_haar_unequal_spin (Q D E : ℕ) (hD : D+2 ≤ Q) (hE : E+2 ≤ Q)
    (hDE : D ≠ E) (r : OddPairLabel D) (s : OddPairLabel E)
    (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s = 0 := by
  rw [fourBody_haar_compressed]
  apply source_unequal_spin_haar_zero
  unfold fourSpinWeight
  omega

theorem fourBody_cross_orbit (Q D : ℕ) (hD : D+2 ≤ Q) (r s : OddPairLabel D)
    (M : Matrix (Fin (fourSpinWeight Q D+1)) (Fin (fourSpinWeight Q D+1)) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (fourBodySpinRepresentation Q)
      (retainedFourInclusion Q D hD r * M * (retainedFourInclusion Q D hD s)ᴴ)) =
      (Matrix.trace M / (4*Q-1-2*D : ℕ)) •
        (retainedFourInclusion Q D hD r * (retainedFourInclusion Q D hD s)ᴴ) := by
  have he (g : SourceSU2) : conjugateOrbit (fourBodySpinRepresentation Q)
      (retainedFourInclusion Q D hD r * M * (retainedFourInclusion Q D hD s)ᴴ) g =
      retainedFourInclusion Q D hD r *
        conjugateOrbit (sourceSpinRepresentation (fourSpinWeight Q D)) M g *
        (retainedFourInclusion Q D hD s)ᴴ := by
    unfold conjugateOrbit
    calc
      _ = (fourBodySpinRepresentation Q g*retainedFourInclusion Q D hD r)*M*
        ((retainedFourInclusion Q D hD s)ᴴ*fourBodySpinRepresentation Q g⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [retainedFourInclusion_SU2,retainedFourInclusion_adjoint_SU2]
        simp only [Matrix.mul_assoc]
  unfold matrixIntegral
  simp_rw [he]
  rw [integral_matrix_sandwich sourceHaar _ (compact_conjugateOrbit_integrable sourceHaar _
    (sourceSpinRepresentation_continuous (fourSpinWeight Q D)) M)]
  change retainedFourInclusion Q D hD r * matrixIntegral sourceHaar
    (conjugateOrbit (sourceSpinRepresentation (fourSpinWeight Q D)) M) *
      (retainedFourInclusion Q D hD s)ᴴ = _
  rw [source_spin_haar_schur,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
  have hd : ((fourSpinWeight Q D+1 : ℕ) : ℂ) = ((4*Q-1-2*D : ℕ) : ℂ) := by
    exact_mod_cast fourSpinWeight_dimension Q D hD
  rw [hd]

end Laughlin.Spin

end OAI
