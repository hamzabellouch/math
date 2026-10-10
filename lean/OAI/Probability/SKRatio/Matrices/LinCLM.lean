import Mathlib
import OAI.Probability.SKRatio.Matrices.EntryLM

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKRatioGaussian.ComplexMatrix
open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ Matrix.frobeniusSeminormedAddCommGroup.toSeminormedAddGroup
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))

def linCLM : Matrix ι ι ℂ →L[ℂ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  (linEquiv (ι := ι)).toLinearMap.toContinuousLinearMap

lemma opNorm_kernelMatrix {g : ℝ → ℂ} (hg : Integrable g)
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (kernelMatrix g M) ≤ ∫ t : ℝ, ‖g t‖ := by
  let : CompleteSpace (EuclideanSpace ℂ ι) := PiLp.completeSpace _ _
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hi := linCLM.integral_comp_comm (kernel_integrable hg M hM)
  change ‖linCLM (∫ t : ℝ, g t • exp (imaginary t M))‖ ≤ _
  calc
    _ = ‖∫ t : ℝ, linCLM (g t • exp (imaginary t M))‖ := congrArg norm hi.symm
    _ ≤ ∫ t : ℝ, ‖linCLM (g t • exp (imaginary t M))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖g t‖ := by
      apply integral_mono (linCLM.integrable_comp (kernel_integrable hg M hM)).norm hg.norm
      intro t
      change ‖lin (g t • exp (imaginary t M))‖ ≤ _
      rw [lin_csmul,norm_smul]
      exact (mul_le_mul_of_nonneg_left (imaginary_exp_opNorm_le t M hM) (norm_nonneg _)).trans_eq (mul_one _)

lemma schwartzMatrix_opNorm (f : 𝓢(ℝ,ℂ)) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (schwartzMatrix f M) ≤ ∫ t : ℝ, ‖(𝓕 f) t‖ :=
  opNorm_kernelMatrix (𝓕 f).integrable _ (by simp [hM])

lemma schwartzMatrix_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hspec : ∀ i, hM.eigenvalues i ∈ Icc lo hi) :
    schwartzMatrix f M = M⁻¹ := by
  rw [schwartzMatrix_spectral f M hM]
  symm
  apply Matrix.inv_eq_left_inv
  conv_lhs => rhs; rw [hM.spectral_theorem]
  change conjugate hM.eigenvectorUnitary (diagonal (fun i => f (hM.eigenvalues i))) *
    conjugate hM.eigenvectorUnitary (diagonal (fun i => (hM.eigenvalues i : ℂ))) = 1
  rw [← map_mul,diagonal_mul_diagonal]
  have hd : diagonal (fun i => f (hM.eigenvalues i) * (hM.eigenvalues i : ℂ)) = (1 : Matrix ι ι ℂ) := by
    have hz (i : ι) : (hM.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le hlo (hspec i).1)
    simp_rw [hf _ (hspec _),inv_mul_cancel₀ (hz _)]
    exact diagonal_one
  rw [hd,map_one]

lemma schwartzMatrix_hermitian (f : 𝓢(ℝ,ℂ)) (hf : ∀ x, star (f x) = f x)
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) : (schwartzMatrix f M).IsHermitian := by
  rw [schwartzMatrix_spectral f M hM]
  change star (conjugate hM.eigenvectorUnitary (diagonal _)) = _
  rw [← map_star]
  congr 1
  change (diagonal (fun i => f (hM.eigenvalues i)))ᴴ = _
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  exact hf (hM.eigenvalues i)

end SKRatioGaussian.ComplexMatrix

end
end
end
end
end
end
end
end
end

end OAI
