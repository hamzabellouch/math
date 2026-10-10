import Mathlib.Probability.Moments.Covariance
import OAI.Geometry.NodalSets.Waves.GaussianPairMoments

namespace OAI

namespace Yau.Geometry
open Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairLinearSum_add (z w : ι → ℂ) :
    pairLinearSum (fun i ↦ z i+w i) = fun a ↦ pairLinearSum z a+pairLinearSum w a := by
  classical
  funext a
  simp only [pairLinearSum,Complex.add_re,Complex.add_im]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

lemma covariance_pairLinearSum (z w : ι → ℂ) :
    cov[pairLinearSum z,pairLinearSum w;gaussianPairs] =
      ∑ i, ((z i).re*(w i).re+(z i).im*(w i).im) := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; infer_instance
  have hz := pairLinearSum_memLp_two z
  have hw := pairLinearSum_memLp_two w
  have hh := variance_add hz hw
  change Var[fun a ↦ pairLinearSum z a+pairLinearSum w a;gaussianPairs] = _ at hh
  rw [← pairLinearSum_add] at hh
  simp only [variance_pairLinearSum] at hh
  have hn : ∑ i, ‖z i+w i‖^2 = (∑ i, ‖z i‖^2) + (∑ i, ‖w i‖^2) +
      2 * ∑ i, ((z i).re*(w i).re+(z i).im*(w i).im) := by
    simp only [← Finset.sum_add_distrib,Finset.mul_sum,Complex.sq_norm,
      Complex.normSq_apply,Complex.add_re,Complex.add_im]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

lemma pairLinearSum_covariance_integral (z w : ι → ℂ) :
    ∫ a, pairLinearSum z a*pairLinearSum w a ∂gaussianPairs =
      ∑ i, ((z i).re*(w i).re+(z i).im*(w i).im) := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; infer_instance
  have hh := covariance_eq_sub (pairLinearSum_memLp_two z) (pairLinearSum_memLp_two w)
  rw [pairLinearSum_mean,pairLinearSum_mean,mul_zero,sub_zero,covariance_pairLinearSum] at hh
  exact hh.symm

end
end Yau.Geometry

end OAI
