import Mathlib
import OAI.Probability.SKRatio.Matrices.LinCLM
import OAI.Probability.SKRatio.Matrices.FourierMoment

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
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ Matrix.frobeniusSeminormedAddCommGroup.toSeminormedAddGroup
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))

lemma opNorm_kernelMatrix_sub {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (M N : Matrix ι ι ℂ) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    opNorm (kernelMatrix g M-kernelMatrix g N) ≤
      (∫ t : ℝ, ‖g t‖*|t|)*opNorm (M-N) := by
  let : CompleteSpace (EuclideanSpace ℂ ι) := PiLp.completeSpace _ _
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  let F := fun t : ℝ => g t • exp (imaginary t M)-g t • exp (imaginary t N)
  have hi : Integrable F := (kernel_integrable hg M hM).sub (kernel_integrable hg N hN)
  have hh := linCLM.integral_comp_comm hi
  have he : kernelMatrix g M-kernelMatrix g N = ∫ t : ℝ, F t := by
    exact (integral_sub (kernel_integrable hg M hM) (kernel_integrable hg N hN)).symm
  rw [he]
  change ‖linCLM (∫ t : ℝ, F t)‖ ≤ _
  calc
    _ = ‖∫ t : ℝ, linCLM (F t)‖ := congrArg norm hh.symm
    _ ≤ ∫ t : ℝ, ‖linCLM (F t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*opNorm (M-N) := by
      apply integral_mono (linCLM.integrable_comp hi).norm (hg₁.mul_const _)
      intro t
      have hb := opNorm_exp_sub (imaginary t M) (imaginary t N) (imaginary_skew t M hM) (imaginary_skew t N hN)
      rw [← imaginary_sub,imaginary_opNorm] at hb
      change opNorm (F t) ≤ _
      dsimp only [F]
      rw [← smul_sub,opNorm_csmul]
      exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_mul_const _ _

lemma schwartzMatrix_opNorm_lipschitz (f : 𝓢(ℝ,ℂ)) (M N : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    opNorm (schwartzMatrix f M-schwartzMatrix f N) ≤
      (2*Real.pi*fourierMoment f 1)*opNorm (M-N) := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := opNorm_kernelMatrix_sub (𝓕 f).integrable hf₁
    ((2*Real.pi:ℝ) • M) ((2*Real.pi:ℝ) • N) (by simp [hM]) (by simp [hN])
  rw [← smul_sub,opNorm_smul,abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

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
