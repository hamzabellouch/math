import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternRotation
import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticCompression
import OAI.Probability.InvariantIsing.Pressure.RandomOrbitLaw

namespace OAI

/-! Pointwise diagonalization of the actual Gaussian-pattern pressure. No
measurable choice of eigenvectors is required for Haar averaging. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma pressure_conjugate_diagonal {N : ℕ} (eig : Fin N → ℝ) (U : Orthogonal N) :
    pressure (cavityConjugate U (Matrix.diagonal eig)) (fun _ => 0)=
      dataPhysicalPressure (eig,fun _ => 0) U := by
  unfold pressure dataPhysicalPressure rotatedPressure
  congr 2
  funext σ
  exact congrArg (fun x => x+fieldEnergy (fun _ => 0) σ)
    (cavityQuadratic_inverse_rotation eig U σ)

lemma gaussianPatternCoupling_smul {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling c z=c • gaussianPatternCoupling 1 z := by
  simp only [gaussianPatternCoupling,smul_smul,one_div]
  rw [div_eq_mul_inv]

lemma cavityConjugate_diagonal_smul {N : ℕ} (c : ℝ) (U : Orthogonal N) (eig : Fin N → ℝ) :
    c • cavityConjugate U (Matrix.diagonal eig)=
      cavityConjugate U (Matrix.diagonal (fun i => c*eig i)) := by
  have hd : Matrix.diagonal (fun i => c*eig i)=c • Matrix.diagonal eig := by
    ext i j
    by_cases h : i=j <;> simp [h]
  rw [hd]
  simp only [cavityConjugate,smul_mul_assoc,mul_smul_comm]

lemma gaussianPattern_diagonalization {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ∃ V : Orthogonal N, gaussianPatternCoupling 1 z=
      cavityConjugate V (Matrix.diagonal (gaussianPatternEigenvalues z)) := by
  let hA := gaussianPatternCoupling_isHermitian 1 z
  refine ⟨hA.eigenvectorUnitary,?_⟩
  simpa [cavityConjugate,Unitary.conjStarAlgAut_apply,Function.comp_def,
    gaussianPatternEigenvalues,hA,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hA.spectral_theorem

lemma gaussianPattern_pressure_orbit {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ∃ V : Orthogonal N, ∀ U : Orthogonal N,
      gaussianPatternPressure c (cavityColumnRotation m (matrixRotation U) z)=
        dataPhysicalPressure ((fun i => c*gaussianPatternEigenvalues z i),fun _ => 0) (U*V) := by
  obtain ⟨V,hV⟩ := gaussianPattern_diagonalization z
  refine ⟨V,fun U => ?_⟩
  rw [gaussianPatternPressure_eq,gaussianPatternCoupling_rotation,
    gaussianPatternCoupling_smul,hV,cavityConjugate_diagonal_smul]
  change pressure (cavityConjugate U (cavityConjugate V
    (Matrix.diagonal (fun i => c*gaussianPatternEigenvalues z i)))) (fun _ => 0)=_
  rw [← cavityConjugate_mul,pressure_conjugate_diagonal]

end InvariantIsing

end

end OAI
