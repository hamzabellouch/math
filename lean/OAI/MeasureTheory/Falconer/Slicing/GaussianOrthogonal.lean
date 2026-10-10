import OAI.MeasureTheory.Falconer.Slicing.GaussianBand
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

namespace OAI

/-! # Orthogonal Gaussian coordinates for random-subspace band estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussian_orthogonal_inner_independent (u v : Space d) (huv : inner ℝ u v = 0) :
    IndepFun (fun x : Space d => inner ℝ u x) (fun x : Space d => inner ℝ v x)
      (stdGaussian (Space d)) := by
  have hpair : HasGaussianLaw (fun x : Space d => (inner ℝ u x,inner ℝ v x))
      (stdGaussian (Space d)) :=
    IsGaussian.hasGaussianLaw_id.map_fun ((innerSL ℝ u).prod (innerSL ℝ v))
  apply hpair.indepFun_of_covariance_eq_zero
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian,
    innerSL_apply_apply,huv]

theorem gaussian_orthogonal_pair_band {u v : Space d} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    stdGaussian (Space d) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ s} ≤
      ENNReal.ofReal (gaussianBandConstant^2*r*s) := by
  have hi := gaussian_orthogonal_inner_independent u v huv
  have he := hi.measure_inter_preimage_eq_mul (Icc (-r) r) (Icc (-s) s)
    measurableSet_Icc measurableSet_Icc
  have hsets (w : Space d) (t : ℝ) :
      (fun x : Space d => inner ℝ w x) ⁻¹' Icc (-t) t = {x | |inner ℝ w x| ≤ t} := by
    ext x
    simp only [mem_preimage,mem_Icc,mem_ofPred_eq,abs_le]
  rw [hsets,hsets] at he
  change stdGaussian (Space d) ({x | |inner ℝ u x| ≤ r} ∩ {x | |inner ℝ v x| ≤ s}) ≤ _
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (gaussianBandConstant*r)*ENNReal.ofReal (gaussianBandConstant*s) :=
      mul_le_mul' (gaussian_unit_inner_band hu hr) (gaussian_unit_inner_band hv hs)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg gaussianBandConstant_pos.le hr)]
      congr 1
      ring

end Falconer

end OAI
