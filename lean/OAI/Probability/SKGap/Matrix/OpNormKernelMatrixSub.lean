import Mathlib
import OAI.Probability.SKGap.Gaussian.FourierMoment

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
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
  let F := fun t : ℝ => g t • exp (imaginary t M)-g t • exp (imaginary t N)
  have hi : Integrable F := (kernel_integrable hg M hM).sub (kernel_integrable hg N hN)
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
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

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_nonneg (M : Matrix ι ι ℂ) : 0 ≤ opNorm M := norm_nonneg _
lemma opNorm_add (M N : Matrix ι ι ℂ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  change ‖linEquiv (M+N)‖ ≤ _
  rw [(linEquiv (ι := ι)).map_add]
  exact norm_add_le _ _
lemma opNorm_sub (M N : Matrix ι ι ℂ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖lin (M-N)‖ ≤ _
  have hh : lin (M-N) = lin M-lin N := linEquiv.map_sub M N
  rw [hh]
  exact norm_sub_le _ _
lemma opNorm_mul (M N : Matrix ι ι ℂ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  change ‖lin (M*N)‖ ≤ _
  rw [lin_mul]
  exact norm_mul_le _ _
lemma opNorm_neg (M : Matrix ι ι ℂ) : opNorm (-M) = opNorm M := by
  change ‖lin (-M)‖ = _
  have hh : lin (-M) = -lin M := linEquiv.map_neg M
  rw [hh,norm_neg]
  rfl
lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  rw [opNorm,lin_one]
  exact ContinuousLinearMap.norm_id_le

lemma sandwich_frobenius (D E : Matrix ι ι ℂ) :
    ‖D*E*D‖ ≤ opNorm D^2*‖E‖ := by
  calc
    _ ≤ ‖D*E‖*opNorm D := frobenius_mul_le_opNorm_right _ _
    _ ≤ (opNorm D*‖E‖)*opNorm D := mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _)
    _ = _ := by ring

lemma sandwich_opNorm (D E : Matrix ι ι ℂ) :
    opNorm (D*E*D) ≤ opNorm D^2*opNorm E := by
  calc
    _ ≤ opNorm (D*E)*opNorm D := opNorm_mul _ _
    _ ≤ (opNorm D*opNorm E)*opNorm D := mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _)
    _ = _ := by ring

lemma sandwich_difference_frobenius (D D' E : Matrix ι ι ℂ) :
    ‖D*E*D-D'*E*D'‖ ≤ (opNorm D+opNorm D')*opNorm (D-D')*‖E‖ := by
  have he : D*E*D-D'*E*D' = (D-D')*E*D+D'*E*(D-D') := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(D-D')*E*D‖+‖D'*E*(D-D')‖ := norm_add_le _ _
    _ ≤ (opNorm (D-D')*‖E‖)*opNorm D+(opNorm D'*‖E‖)*opNorm (D-D') := by
      apply add_le_add
      · exact (frobenius_mul_le_opNorm_right _ _).trans
          (mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _))
      · exact (frobenius_mul_le_opNorm_right _ _).trans
          (mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _))
    _ = _ := by ring

lemma sandwich_difference_opNorm (D D' E : Matrix ι ι ℂ) :
    opNorm (D*E*D-D'*E*D') ≤ (opNorm D+opNorm D')*opNorm (D-D')*opNorm E := by
  have he : D*E*D-D'*E*D' = (D-D')*E*D+D'*E*(D-D') := by noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm ((D-D')*E*D)+opNorm (D'*E*(D-D')) := opNorm_add _ _
    _ ≤ (opNorm (D-D')*opNorm E)*opNorm D+(opNorm D'*opNorm E)*opNorm (D-D') := by
      apply add_le_add
      · exact (opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _))
      · exact (opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _))
    _ = _ := by ring

lemma product_four_point (a b c d e f g h : Matrix ι ι ℂ) :
    ‖(a*e-b*f)-(c*g-d*h)‖ ≤
      ‖(a-b)-(c-d)‖*opNorm e + ‖c-d‖*opNorm (e-g) +
      opNorm (b-d)*‖e-f‖ + opNorm d*‖(e-f)-(g-h)‖ := by
  have he : (a*e-b*f)-(c*g-d*h) =
      ((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)+d*((e-f)-(g-h)) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)‖+‖d*((e-f)-(g-h))‖ := norm_add_le _ _
    _ ≤ (‖((a-b)-(c-d))*e+(c-d)*(e-g)‖+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖((a-b)-(c-d))*e‖+‖(c-d)*(e-g)‖)+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      gcongr
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm _ _
      · exact frobenius_mul_le_opNorm _ _

end SKGap.ComplexMatrix

end

end OAI
