import Mathlib
import OAI.Probability.SKRatio.Matrices.ExpDuhamel
import OAI.Probability.SKRatio.Matrices.LinEquiv

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
  let : CompleteSpace (EuclideanSpace ℂ ι) := PiLp.completeSpace _ _
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  let : NormedAlgebra ℚ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := .restrictScalars ℚ ℝ _
  have hh := SKRatioGaussian.exp_skew_difference (lin M) (lin N) hMl hNl
  simpa only [opNorm,lin_sub,lin_exp] using hh

lemma frobenius_exp_sub (M N : Matrix ι ι ℂ) (hM : Mᴴ = -M) (hN : Nᴴ = -N) :
    ‖exp M-exp N‖ ≤ ‖M-N‖ := by
  rw [show exp M-exp N = _ from SKRatioGaussian.exp_duhamel M N]
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
  rw [show exp a-exp b = _ from SKRatioGaussian.exp_duhamel a b, show exp c-exp d = _ from SKRatioGaussian.exp_duhamel c d]
  change ‖(∫ u : ℝ in (0 : ℝ)..1, F a b u)-(∫ u : ℝ in (0 : ℝ)..1, F c d u)‖ ≤ _
  rw [← intervalIntegral.integral_sub ((hF a b).intervalIntegrable 0 1) ((hF c d).intervalIntegrable 0 1)]
  calc
    _ ≤ ∫ u : ℝ in (0 : ℝ)..1, ‖F a b u-F c d u‖ := intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _ : ℝ in (0 : ℝ)..1, ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num) (((hF a b).sub (hF c d)).norm.intervalIntegrable 0 1)
        (intervalIntegrable_const)
      exact hbound
    _ = _ := by simp

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
