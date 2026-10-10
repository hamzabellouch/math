import Mathlib
import OAI.Probability.SKGap.Matrix.LipschitzNormedConvolution

namespace OAI

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
namespace SKGap
section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_mgf_lipschitz_le {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
        exp (2 * |r| * ((L : ℝ) * ε)) * exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
    obtain ⟨g, hgs, hgl, hgf⟩ := exists_smooth_lipschitz_approx hf hε
    have hmg := stdGaussian_mgf_centered_le
      (fun x => (hgs.differentiable (by simp) x).hasFDerivAt)
      (hgs.continuous_fderiv (by simp)) (fun _ => norm_fderiv_le_of_lipschitz ℝ hgl) r
    exact (centered_mgf_le_of_uniform_dist hf hgl
      (fun x => by simpa only [dist_comm] using hgf x) r).trans
        (mul_le_mul_of_nonneg_left hmg (exp_pos _).le)
  have ht : Tendsto (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) (𝓝[>] 0)
      (𝓝 (exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8))) := by
    have hc : Continuous (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) := by fun_prop
    simpa using ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε heps
  exact hε ε heps

theorem stdGaussian_upper_tail_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | u ≤ f x - ∫ y, f y ∂stdGaussian E} ≤
      exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
  let t : ℝ := 4 * u / (π ^ 2 * (L : ℝ) ^ 2)
  have hLr : 0 < (L : ℝ) := hL
  have hden : 0 < π ^ 2 * (L : ℝ) ^ 2 := mul_pos (sq_pos_of_pos pi_pos) (sq_pos_of_pos hLr)
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (by norm_num) hu) hden.le
  have hi : Integrable (fun x => exp (t * (f x - ∫ y, f y ∂stdGaussian E)))
      (stdGaussian E) := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hf t).const_mul _
  calc
    _ ≤ exp (-t * u) * ∫ x, exp (t * (f x - ∫ y, f y ∂stdGaussian E))
        ∂stdGaussian E := measure_ge_le_exp_mul_mgf u ht hi
    _ ≤ exp (-t * u) * exp (π ^ 2 * t ^ 2 * (L : ℝ) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (stdGaussian_mgf_lipschitz_le hf t) (exp_pos _).le
    _ = exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
      rw [← exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

theorem stdGaussian_lower_tail_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | f x - ∫ y, f y ∂stdGaussian E ≤ -u} ≤
      exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
  have h := stdGaussian_upper_tail_lipschitz hf.neg hL hu
  have he : {x | (fun x => -f x) x - ∫ y, -f y ∂stdGaussian E ≥ u} =
      {x | f x - ∫ y, f y ∂stdGaussian E ≤ -u} := by
    ext x
    simp only [mem_ofPred_eq, integral_neg]
    constructor <;> intro hx <;> linarith
  simp only [Pi.neg_apply] at h
  rw [he] at h
  exact h

theorem stdGaussian_tail_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | u ≤ |f x - ∫ y, f y ∂stdGaussian E|} ≤
      2 * exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
  have he : {x | u ≤ |f x - ∫ y, f y ∂stdGaussian E|} =
      {x | u ≤ f x - ∫ y, f y ∂stdGaussian E} ∪
      {x | f x - ∫ y, f y ∂stdGaussian E ≤ -u} := by
    ext x
    simp only [mem_union, mem_ofPred_eq, le_abs]
    constructor <;> rintro (hx | hx)
    · exact Or.inl hx
    · right; linarith
    · exact Or.inl hx
    · right; linarith
  rw [he]
  calc
    _ ≤ (stdGaussian E).real {x | u ≤ f x - ∫ y, f y ∂stdGaussian E} +
        (stdGaussian E).real {x | f x - ∫ y, f y ∂stdGaussian E ≤ -u} :=
      measureReal_union_le _ _
    _ ≤ exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) +
        exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) :=
      add_le_add (stdGaussian_upper_tail_lipschitz hf hL hu)
        (stdGaussian_lower_tail_lipschitz hf hL hu)
    _ = _ := by ring

end StandardGaussianRotation
end SKGap

end
end
end
end
end

end OAI
