import Mathlib
import OAI.Probability.SKGap.Localization.ExpDuhamel

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
open MeasureTheory Set NormedSpace
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lin_sub (M N : Matrix ι ι ℂ) : lin (M-N) = lin M - lin N := linEquiv.map_sub M N
lemma lin_neg (M : Matrix ι ι ℂ) : lin (-M) = - lin M := linEquiv.map_neg M
lemma opNorm_smul (t : ℝ) (M : Matrix ι ι ℂ) : opNorm (t • M) = |t| * opNorm M := by
  change ‖lin (t • M)‖ = _
  have hh : lin (t • M) = t • lin M := by ext x i; simp [lin,Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.smul_mulVec]
  rw [hh,norm_smul,Real.norm_eq_abs]
  rfl

lemma unitary_exp_smul (M : Matrix ι ι ℂ) (hM : Mᴴ = -M) (u : ℝ) :
    exp (u • M) ∈ unitary (Matrix ι ι ℂ) := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  change (u • M)ᴴ = -(u • M)
  simp [hM]

lemma opNorm_exp_sub (M N : Matrix ι ι ℂ) (hM : Mᴴ = -M) (hN : Nᴴ = -N) :
    opNorm (exp M-exp N) ≤ opNorm (M-N) := by
  have hMl : star (lin M) = -lin M := by rw [ContinuousLinearMap.star_eq_adjoint,← lin_adjoint,hM,lin_neg]
  have hNl : star (lin N) = -lin N := by rw [ContinuousLinearMap.star_eq_adjoint,← lin_adjoint,hN,lin_neg]
  let : NormedAlgebra ℚ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := .restrictScalars ℚ ℝ _
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hh := SKGap.exp_skew_difference (lin M) (lin N) hMl hNl
  simpa only [opNorm,lin_sub,lin_exp] using hh

lemma frobenius_exp_sub (M N : Matrix ι ι ℂ) (hM : Mᴴ = -M) (hN : Nᴴ = -N) :
    ‖exp M-exp N‖ ≤ ‖M-N‖ := by
  rw [show exp M-exp N = _ from SKGap.exp_duhamel M N]
  have hh (u : ℝ) : ‖exp ((1-u) • M) * (M-N) * exp (u • N)‖ = ‖M-N‖ := by
    rw [frobenius_mul_unitary _ _ (unitary_exp_smul N hN u),
      frobenius_unitary_mul _ _ (unitary_exp_smul M hM (1-u))]
  calc
    _ ≤ ∫ u : ℝ in (0 : ℝ)..1, ‖exp ((1-u) • M) * (M-N) * exp (u • N)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ‖M-N‖ := by simp only [hh]; simp

lemma exp_four_point (a b c d : Matrix ι ι ℂ)
    (ha : aᴴ = -a) (hb : bᴴ = -b) (hc : cᴴ = -c) (hd : dᴴ = -d) :
    ‖(exp a-exp b)-(exp c-exp d)‖ ≤
      ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  let F := fun a b : Matrix ι ι ℂ => fun u : ℝ => exp ((1-u) • a) * (a-b) * exp (u • b)
  have hF (a b : Matrix ι ι ℂ) : Continuous (F a b) := by dsimp [F]; fun_prop
  have hbound (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖F a b u-F c d u‖ ≤ ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
    have hsa : ((1-u) • a)ᴴ = -((1-u) • a) := by simp [ha]
    have hsc : ((1-u) • c)ᴴ = -((1-u) • c) := by simp [hc]
    have hsb : (u • b)ᴴ = -(u • b) := by simp [hb]
    have hsd : (u • d)ᴴ = -(u • d) := by simp [hd]
    have h₁ := opNorm_exp_sub ((1-u) • a) ((1-u) • c) hsa hsc
    have h₂ := opNorm_exp_sub (u • b) (u • d) hsb hsd
    rw [← smul_sub,opNorm_smul,abs_of_nonneg (sub_nonneg.mpr hu.2)] at h₁
    rw [← smul_sub,opNorm_smul,abs_of_nonneg hu.1] at h₂
    have ha0 : 0 ≤ opNorm (a-c) := norm_nonneg _
    have hb0 : 0 ≤ opNorm (b-d) := norm_nonneg _
    have h₁' : opNorm (exp ((1-u) • a)-exp ((1-u) • c)) ≤ opNorm (a-c) := by nlinarith [hu.1]
    have h₂' : opNorm (exp (u • b)-exp (u • d)) ≤ opNorm (b-d) := by nlinarith [hu.2]
    have hid : F a b u-F c d u =
        exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b) +
        (exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b) +
        exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d)) := by dsimp [F]; noncomm_ring
    rw [hid]
    have hfirst : ‖exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b)‖ = ‖(a-b)-(c-d)‖ := by
      rw [frobenius_mul_unitary _ _ (unitary_exp_smul b hb u),
        frobenius_unitary_mul _ _ (unitary_exp_smul a ha (1-u))]
    have hsecond : ‖(exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b)‖ ≤ opNorm (a-c)*‖c-d‖ := by
      rw [frobenius_mul_unitary _ _ (unitary_exp_smul b hb u)]
      exact (frobenius_mul_le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h₁' (norm_nonneg _))
    have hthird : ‖exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d))‖ ≤ opNorm (b-d)*‖c-d‖ := by
      rw [mul_assoc,frobenius_unitary_mul _ _ (unitary_exp_smul c hc (1-u))]
      exact (frobenius_mul_le_opNorm_right _ _).trans (by nlinarith [norm_nonneg (c-d)])
    calc
      _ ≤ ‖exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b)‖ +
        ‖(exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b)‖ +
        ‖exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d))‖ := norm_add₃_le
      _ ≤ _ := by rw [hfirst]; nlinarith
  rw [show exp a-exp b = _ from SKGap.exp_duhamel a b, show exp c-exp d = _ from SKGap.exp_duhamel c d]
  change ‖(∫ u : ℝ in (0 : ℝ)..1, F a b u)-(∫ u : ℝ in (0 : ℝ)..1, F c d u)‖ ≤ _
  rw [← intervalIntegral.integral_sub ((hF a b).intervalIntegrable 0 1) ((hF c d).intervalIntegrable 0 1)]
  calc
    _ ≤ ∫ u : ℝ in (0 : ℝ)..1, ‖F a b u-F c d u‖ := intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _ : ℝ in (0 : ℝ)..1, ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num) (((hF a b).sub (hF c d)).norm.intervalIntegrable 0 1)
        (intervalIntegrable_const)
      exact hbound
    _ = _ := by simp

end

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

end SKGap.ComplexMatrix

end

end OAI
