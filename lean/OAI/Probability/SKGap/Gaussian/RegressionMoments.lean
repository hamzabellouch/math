import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianDisintegration

namespace OAI

section
noncomputable section
namespace SKGap.GaussianRegression
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
  {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}

lemma residual_mean_zero (hXY : HasGaussianLaw (fun w => (X w,Y w)) P)
    (K : Matrix ι κ ℝ) (hx : ∀ i, (∫ w, X w i ∂P)=0)
    (hy : ∀ k, (∫ w, Y w k ∂P)=0) (i : ι) :
    (∫ w, (X w-K*ᵥY w) i ∂P)=0 := by
  have hK : Integrable (fun w => ∑ k,K i k*Y w k) P :=
    ((hXY.snd.map (matrixCLM K)).eval i).integrable
  change (∫ w, X w i-∑ k, K i k*Y w k ∂P)=0
  rw [integral_sub (hXY.fst.eval i).integrable hK,
    integral_finsetSum _ (fun k _ => (hXY.snd.eval k).integrable.const_mul _)]
  simp only [integral_const_mul,hx,hy,mul_zero,Finset.sum_const_zero,sub_zero]

lemma residual_cross_covariance (hXY : HasGaussianLaw (fun w => (X w,Y w)) P)
    (K : Matrix ι κ ℝ)
    (hc : ∀ i k, cov[fun w => X w i,fun w => Y w k;P]=
      ∑ l, K i l*cov[fun w => Y w l,fun w => Y w k;P]) (i : ι) (k : κ) :
    cov[fun w => (X w-K*ᵥY w) i,fun w => Y w k;P]=0 := by
  have := hXY.isProbabilityMeasure
  have hK : MemLp (fun w => ∑ l,K i l*Y w l) 2 P :=
    ((hXY.snd.map (matrixCLM K)).eval i).memLp_two
  change cov[fun w => X w i-∑ l,K i l*Y w l,fun w => Y w k;P]=0
  rw [covariance_fun_sub_left (hXY.fst.eval i).memLp_two hK (hXY.snd.eval k).memLp_two,
    covariance_fun_sum_left (fun l => (hXY.snd.eval l).memLp_two.const_mul _) (hXY.snd.eval k).memLp_two]
  simp only [covariance_const_mul_left,hc,sub_self]

lemma residual_covariance (hXY : HasGaussianLaw (fun w => (X w,Y w)) P)
    (K : Matrix ι κ ℝ)
    (hc : ∀ i k, cov[fun w => X w i,fun w => Y w k;P]=
      ∑ l, K i l*cov[fun w => Y w l,fun w => Y w k;P]) (i k : ι) :
    cov[fun w => (X w-K*ᵥY w) i,fun w => (X w-K*ᵥY w) k;P]=
      cov[fun w => X w i,fun w => X w k;P]-
      ∑ l, K i l*cov[fun w => Y w l,fun w => X w k;P] := by
  have := hXY.isProbabilityMeasure
  have hR := (residual_joint_gaussian hXY K).fst
  have hK (q : ι) : MemLp (fun w => ∑ l,K q l*Y w l) 2 P :=
    ((hXY.snd.map (matrixCLM K)).eval q).memLp_two
  change cov[fun w => (X w-K*ᵥY w) i,fun w => X w k-∑ l,K k l*Y w l;P]=_
  rw [covariance_fun_sub_right (hR.eval i).memLp_two (hXY.fst.eval k).memLp_two (hK k),
    covariance_fun_sum_right (fun l => (hXY.snd.eval l).memLp_two.const_mul _) (hR.eval i).memLp_two]
  simp only [covariance_const_mul_right,residual_cross_covariance hXY K hc,mul_zero,
    Finset.sum_const_zero,sub_zero]
  change cov[fun w => X w i-∑ l,K i l*Y w l,fun w => X w k;P]=_
  rw [covariance_fun_sub_left (hXY.fst.eval i).memLp_two (hK i) (hXY.fst.eval k).memLp_two,
    covariance_fun_sum_left (fun l => (hXY.snd.eval l).memLp_two.const_mul _) (hXY.fst.eval k).memLp_two]
  simp only [covariance_const_mul_left]

end SKGap.GaussianRegression
end
end

end OAI
