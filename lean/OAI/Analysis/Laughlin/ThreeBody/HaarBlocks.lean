import OAI.Analysis.Laughlin.Spin.HaarOrthogonality
import OAI.Analysis.Laughlin.Spin.Sandwich
import OAI.Analysis.Laughlin.ThreeBody.GroupIntertwining

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker
open Rotation MeasureTheory

noncomputable def threeBodySpinRepresentation (Q : ℕ) :
    SourceSU2 →* Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ where
  toFun g := sourceSpinRepresentation (2*Q-2) g ⊗ₖ sourceSpinRepresentation Q g
  map_one' := by simp only [map_one,Matrix.one_kronecker_one]
  map_mul' g h := by simp only [map_mul,Matrix.mul_kronecker_mul]

theorem threeBodySpinRepresentation_continuous (Q : ℕ) (i j : PairOrbitalIndex Q) :
    Continuous (fun g => threeBodySpinRepresentation Q g i j) :=
  (sourceSpinRepresentation_continuous (2*Q-2) i.1 j.1).mul
    (sourceSpinRepresentation_continuous Q i.2 j.2)

theorem threeBodySpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    threeBodySpinRepresentation Q g⁻¹=(threeBodySpinRepresentation Q g)ᴴ := by
  change _ ⊗ₖ _ = (_ ⊗ₖ _)ᴴ
  rw [Matrix.conjTranspose_kronecker,sourceSpinRepresentation_inv,sourceSpinRepresentation_inv]

theorem threeCoupledInclusion_adjoint_SU2 (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (g : SourceSU2) :
    (threeCoupledInclusion Q hQ z)ᴴ * threeBodySpinRepresentation Q g =
      sourceSpinRepresentation (coupledWeight Q z.val) g * (threeCoupledInclusion Q hQ z)ᴴ := by
  have h : threeBodySpinRepresentation Q g⁻¹ * threeCoupledInclusion Q hQ z =
    threeCoupledInclusion Q hQ z * sourceSpinRepresentation (coupledWeight Q z.val) g⁻¹ :=
    threeCoupledInclusion_SU2 Q hQ z g⁻¹
  have ht := congrArg Matrix.conjTranspose h
  simpa only [Matrix.conjTranspose_mul,threeBodySpinRepresentation_inv,sourceSpinRepresentation_inv,
    Matrix.conjTranspose_conjTranspose] using ht

theorem threeBody_haar_compressed (Q : ℕ) (hQ : 2 ≤ Q) (z w : Fin (Q+1))
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    (threeCoupledInclusion Q hQ z)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ w =
    rectangularIntegral sourceHaar (rectangularOrbit
      (sourceSpinRepresentation (coupledWeight Q z.val))
      (sourceSpinRepresentation (coupledWeight Q w.val))
      ((threeCoupledInclusion Q hQ z)ᴴ*M*threeCoupledInclusion Q hQ w)) := by
  change (threeCoupledInclusion Q hQ z)ᴴ * entrywiseIntegral sourceHaar
    (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ w = _
  rw [← integral_matrix_sandwich sourceHaar _
    (compact_conjugateOrbit_integrable sourceHaar _ (threeBodySpinRepresentation_continuous Q) M)]
  funext i j
  apply integral_congr_ae
  filter_upwards [] with g
  have hw : threeBodySpinRepresentation Q g⁻¹*threeCoupledInclusion Q hQ w =
    threeCoupledInclusion Q hQ w*sourceSpinRepresentation (coupledWeight Q w.val) g⁻¹ :=
    threeCoupledInclusion_SU2 Q hQ w g⁻¹
  simp only [conjugateOrbit,rectangularOrbit]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,threeCoupledInclusion_adjoint_SU2,
    Matrix.mul_assoc,Matrix.mul_assoc,hw]
  simp only [Matrix.mul_assoc]

theorem threeBody_haar_diagonal_block (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    (threeCoupledInclusion Q hQ z)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ z =
      (Matrix.trace ((threeSpinProjector Q hQ z).map Complex.ofReal*M)/
        (coupledWeight Q z.val+1 : ℕ)) • 1 := by
  rw [threeBody_haar_compressed,source_equal_spin_haar_trace]
  congr 2
  rw [threeSpinProjector_complex_factor]
  calc
    _ = Matrix.trace (threeCoupledInclusion Q hQ z*((threeCoupledInclusion Q hQ z)ᴴ*M)) :=
      Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem threeBody_haar_offdiagonal_block (Q : ℕ) (hQ : 2 ≤ Q) (z w : Fin (Q+1))
    (hzw : z ≠ w) (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    (threeCoupledInclusion Q hQ z)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ w = 0 := by
  rw [threeBody_haar_compressed]
  apply source_unequal_spin_haar_zero
  intro h
  apply hzw
  apply Fin.ext
  unfold coupledWeight at h
  have hz := z.isLt
  have hw := w.isLt
  omega

end Laughlin.Spin

end OAI
