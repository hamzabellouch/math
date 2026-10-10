import Mathlib
import OAI.Probability.SKRatio.Matrices.Imaginary

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

def entryLM (i j : ι) : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun := fun M => M i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def entryCLM (i j : ι) : Matrix ι ι ℂ →L[ℂ] ℂ := (entryLM i j).toContinuousLinearMap

lemma integral_entry {F : ℝ → Matrix ι ι ℂ} (hF : Integrable F) (i j : ι) :
    (∫ t : ℝ, F t) i j = ∫ t : ℝ, F t i j := by
  exact ((entryCLM i j).integral_comp_comm hF).symm

def conjugate (U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U

def conjugateCLM (U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
  (conjugate U).toAlgEquiv.toLinearMap.toContinuousLinearMap

lemma conjugate_exp (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    conjugate U (exp M) = exp (conjugate U M) := by
  exact NormedSpace.map_exp (conjugate U).toRingHom (conjugateCLM U).continuous M

lemma conjugate_imaginary (U : unitary (Matrix ι ι ℂ)) (t : ℝ) (M : Matrix ι ι ℂ) :
    conjugate U (imaginary t M) = imaginary t (conjugate U M) := by
  exact (conjugate U).map_smul' _ _

lemma kernelMatrix_conjugate {g : ℝ → ℂ} (hg : Integrable g) (U : unitary (Matrix ι ι ℂ))
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    kernelMatrix g (conjugate U M) = conjugate U (kernelMatrix g M) := by
  have hi := (conjugateCLM U).integral_comp_comm (kernel_integrable hg M hM)
  change _ = (conjugateCLM U) (∫ t : ℝ, g t • exp (imaginary t M))
  calc
    _ = ∫ t : ℝ, (conjugateCLM U) (g t • exp (imaginary t M)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      change g t • exp (imaginary t (conjugate U M)) = conjugate U (g t • exp (imaginary t M))
      rw [map_smul,conjugate_exp,conjugate_imaginary]
    _ = _ := hi

lemma kernelMatrix_diagonal {g : ℝ → ℂ} (hg : Integrable g) (x : ι → ℝ) :
    kernelMatrix g (diagonal (fun i => (x i : ℂ))) =
      diagonal (fun i => ∫ t : ℝ, g t * Complex.exp ((t : ℂ)*Complex.I*(x i : ℂ))) := by
  have hD : (diagonal (fun i => (x i : ℂ)))ᴴ = diagonal (fun i => (x i : ℂ)) := by
    simp [Matrix.diagonal_conjTranspose]
  ext i j
  rw [kernelMatrix,integral_entry (kernel_integrable hg _ hD)]
  have hexp (t : ℝ) : exp (imaginary t (diagonal (fun i => (x i : ℂ)))) =
      diagonal (fun i => Complex.exp ((t : ℂ)*Complex.I*(x i : ℂ))) := by
    rw [imaginary,← diagonal_smul,Matrix.exp_diagonal]
    congr 1
    ext i
    rw [Pi.coe_exp,← Complex.exp_eq_exp_ℂ]
    rfl
  simp_rw [hexp,Matrix.smul_apply,smul_eq_mul]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

noncomputable def schwartzMatrix (f : 𝓢(ℝ, ℂ)) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  kernelMatrix ((𝓕 f : 𝓢(ℝ,ℂ)) : ℝ → ℂ) ((2*Real.pi : ℝ) • M)

lemma fourier_scalar_inverse (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ t : ℝ, (𝓕 f) t * Complex.exp ((t : ℂ)*Complex.I*((2*Real.pi*x : ℝ) : ℂ))) = f x := by
  have hh := congrArg (fun g : 𝓢(ℝ,ℂ) => g x) (show (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ)) = f from FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq'] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul,Real.inner_apply]
  conv_lhs => rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

lemma schwartzMatrix_diagonal (f : 𝓢(ℝ,ℂ)) (x : ι → ℝ) :
    schwartzMatrix f (diagonal (fun i => (x i : ℂ))) = diagonal (fun i => f (x i)) := by
  rw [schwartzMatrix,← diagonal_smul]
  have heq : (2*Real.pi : ℝ) • (fun i => (x i : ℂ)) = fun i => ((2*Real.pi*x i : ℝ) : ℂ) := by
    ext i; simp
  rw [heq,kernelMatrix_diagonal (𝓕 f).integrable]
  congr 1
  ext i
  exact fourier_scalar_inverse f (x i)

lemma schwartzMatrix_conjugate (f : 𝓢(ℝ,ℂ)) (U : unitary (Matrix ι ι ℂ))
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    schwartzMatrix f (conjugate U M) = conjugate U (schwartzMatrix f M) := by
  have heq : (2*Real.pi : ℝ) • conjugate U M = conjugate U ((2*Real.pi : ℝ) • M) := by
    simp [conjugate,Unitary.conjStarAlgAut_apply]
  rw [schwartzMatrix,heq]
  exact kernelMatrix_conjugate (𝓕 f).integrable U _ (by simp [hM])

lemma schwartzMatrix_spectral (f : 𝓢(ℝ,ℂ)) (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    schwartzMatrix f M = conjugate hM.eigenvectorUnitary (diagonal (fun i => f (hM.eigenvalues i))) := by
  conv_lhs => rw [hM.spectral_theorem]
  change schwartzMatrix f (conjugate hM.eigenvectorUnitary (diagonal (fun i => (hM.eigenvalues i : ℂ)))) = _
  rw [schwartzMatrix_conjugate f _ _ (by simp [Matrix.diagonal_conjTranspose]),schwartzMatrix_diagonal]

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
