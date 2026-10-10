import Mathlib
import OAI.Probability.SKRatio.Matrices.LinSub

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

lemma lin_csmul (z : ℂ) (M : Matrix ι ι ℂ) : lin (z • M) = z • lin M :=
  (linEquiv (ι := ι)).map_smul z M

lemma opNorm_csmul (z : ℂ) (M : Matrix ι ι ℂ) : opNorm (z • M) = ‖z‖ * opNorm M := by
  simp only [opNorm,lin_csmul,norm_smul]

noncomputable def imaginary (t : ℝ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((t : ℂ)*Complex.I) • M

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_skew (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    (imaginary t M)ᴴ = -(imaginary t M) := by
  simp [imaginary,Matrix.conjTranspose_smul,hM,star_mul,mul_comm]

lemma imaginary_norm (t : ℝ) (M : Matrix ι ι ℂ) : ‖imaginary t M‖ = |t| * ‖M‖ := by
  simp [imaginary,norm_smul]

lemma imaginary_opNorm (t : ℝ) (M : Matrix ι ι ℂ) : opNorm (imaginary t M) = |t| * opNorm M := by
  simp [imaginary,opNorm_csmul]

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_sub (t : ℝ) (M N : Matrix ι ι ℂ) :
    imaginary t (M-N) = imaginary t M-imaginary t N := by simp [imaginary,smul_sub]

lemma imaginary_exp_unitary (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    exp (imaginary t M) ∈ unitary (Matrix ι ι ℂ) := by
  simpa using unitary_exp_smul _ (imaginary_skew t M hM) 1

lemma imaginary_exp_norm (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    ‖exp (imaginary t M)‖ = ‖(1 : Matrix ι ι ℂ)‖ := by
  simpa using frobenius_unitary_mul (exp (imaginary t M)) 1 (imaginary_exp_unitary t M hM)

lemma imaginary_exp_opNorm_le (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (exp (imaginary t M)) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (lin_unitary _ (imaginary_exp_unitary t M hM))]
  simp

noncomputable def kernelMatrix (g : ℝ → ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∫ t : ℝ, g t • exp (imaginary t M)

lemma kernel_integrable {g : ℝ → ℂ} (hg : Integrable g) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    Integrable (fun t : ℝ => g t • exp (imaginary t M)) := by
  have hc : Continuous (fun t : ℝ => exp (imaginary t M)) := by dsimp [imaginary]; fun_prop
  apply (hg.norm.mul_const ‖(1 : Matrix ι ι ℂ)‖).mono' (hg.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖g t • exp (imaginary t M)‖ ≤ _
  rw [norm_smul,imaginary_exp_norm t M hM]

lemma kernelMatrix_lipschitz {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (M N : Matrix ι ι ℂ) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖kernelMatrix g M-kernelMatrix g N‖ ≤ (∫ t : ℝ, ‖g t‖*|t|) * ‖M-N‖ := by
  rw [kernelMatrix,kernelMatrix,← integral_sub (kernel_integrable hg M hM) (kernel_integrable hg N hN)]
  calc
    _ ≤ ∫ t : ℝ, ‖g t • exp (imaginary t M)-g t • exp (imaginary t N)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*‖M-N‖ := by
      apply integral_mono ((kernel_integrable hg M hM).sub (kernel_integrable hg N hN)).norm (hg₁.mul_const _)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← smul_sub,norm_smul]
      have hh := frobenius_exp_sub _ _ (imaginary_skew t M hM) (imaginary_skew t N hN)
      rw [← imaginary_sub,imaginary_norm] at hh
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
    _ = _ := integral_mul_const _ _

lemma kernelMatrix_four_point {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (hg₂ : Integrable (fun t : ℝ => ‖g t‖*|t|^2))
    (a b c d : Matrix ι ι ℂ) (ha : aᴴ = a) (hb : bᴴ = b) (hc : cᴴ = c) (hd : dᴴ = d) :
    ‖(kernelMatrix g a-kernelMatrix g b)-(kernelMatrix g c-kernelMatrix g d)‖ ≤
      (∫ t : ℝ, ‖g t‖*|t|)*‖(a-b)-(c-d)‖ +
      (∫ t : ℝ, ‖g t‖*|t|^2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  let F := fun (M : Matrix ι ι ℂ) (t : ℝ) => g t • exp (imaginary t M)
  have hi (M : Matrix ι ι ℂ) (hM : Mᴴ = M) : Integrable (F M) := kernel_integrable hg M hM
  have hi' := ((hi a ha).sub (hi b hb)).sub ((hi c hc).sub (hi d hd))
  change ‖((∫ t, F a t)-(∫ t, F b t))-((∫ t, F c t)-(∫ t, F d t))‖ ≤ _
  rw [← integral_sub (hi a ha) (hi b hb),← integral_sub (hi c hc) (hi d hd),
    ← integral_sub (f := fun t => F a t-F b t) (g := fun t => F c t-F d t)
      ((hi a ha).sub (hi b hb)) ((hi c hc).sub (hi d hd))]
  calc
    _ ≤ ∫ t : ℝ, ‖(F a t-F b t)-(F c t-F d t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*‖(a-b)-(c-d)‖ +
        (‖g t‖*|t|^2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
      apply integral_mono hi'.norm ((hg₁.mul_const _).add ((hg₂.mul_const _).mul_const _))
      intro t
      dsimp only [F,Pi.sub_apply]
      rw [← smul_sub,← smul_sub,← smul_sub,norm_smul]
      have hh := exp_four_point (imaginary t a) (imaginary t b) (imaginary t c) (imaginary t d)
        (imaginary_skew t a ha) (imaginary_skew t b hb) (imaginary_skew t c hc) (imaginary_skew t d hd)
      simp only [← imaginary_sub,imaginary_norm,imaginary_opNorm] at hh
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by dsimp only [Pi.add_apply]; ring)
    _ = _ := by rw [integral_add (hg₁.mul_const _) ((hg₂.mul_const _).mul_const _)]; simp only [integral_mul_const]

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
