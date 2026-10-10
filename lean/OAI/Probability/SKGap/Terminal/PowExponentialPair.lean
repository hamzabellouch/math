import Mathlib
import OAI.Probability.SKGap.Gaussian.StdGaussianMgfLipschitz

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
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section SubgaussianMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

lemma pow_le_exponential_pair (x : ℝ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    |x|^k ≤ ((k.factorial : ℝ)/r^k) * (exp (r*x)+exp (-r*x)) := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hh := Real.pow_div_factorial_le_exp (r*|x|) (mul_nonneg hr.le (abs_nonneg x)) k
  have he : exp (r*|x|) ≤ exp (r*x)+exp (-r*x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (exp_nonneg _)
    · rw [abs_of_nonpos hx]; have hid : r * -x = -r*x := by ring
      rw [hid]; exact le_add_of_nonneg_left (exp_nonneg _)
  have hg := hh.trans he
  rw [div_le_iff₀ hk,mul_pow] at hg
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hr k)).mpr
  convert hg using 1 <;> ring

lemma subgaussian_abs_moment {r : ℝ} (hr : 0 < r) (hX : HasSubgaussianMGF X c μ) (k : ℕ) :
    (∫ x, |X x|^k ∂μ) ≤
      2*((k.factorial : ℝ)/r^k)*exp ((c : ℝ)*r^2/2) := by
  let C := (k.factorial : ℝ)/r^k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : Integrable (fun x => C*(exp (r*X x)+exp (-r*X x))) μ :=
    ((hX.integrable_exp_mul r).add (hX.integrable_exp_mul (-r))).const_mul C
  have hp (x : Ω) : |X x|^k ≤ C*(exp (r*X x)+exp (-r*X x)) := pow_le_exponential_pair (X x) hr k
  have hi : Integrable (fun x => |X x|^k) μ := by
    apply he.mono' (hX.integrable.aestronglyMeasurable.norm.pow k)
    filter_upwards [] with x
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_abs] using hp x
  calc
    _ ≤ ∫ x, C*(exp (r*X x)+exp (-r*X x)) ∂μ := integral_mono hi he hp
    _ = C*(mgf X μ r+mgf X μ (-r)) := by
      rw [integral_const_mul,integral_add (hX.integrable_exp_mul r) (hX.integrable_exp_mul (-r))]
      rfl
    _ ≤ C*(exp ((c:ℝ)*r^2/2)+exp ((c:ℝ)*r^2/2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [neg_sq] using add_le_add (hX.mgf_le r) (hX.mgf_le (-r))
    _ = _ := by dsimp only [C]; ring
end SubgaussianMoments

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_subgaussian_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂stdGaussian E)
      ⟨π^2*(L:ℝ)^2/4,by positivity⟩ (stdGaussian E) where
  integrable_exp_mul r := by
    apply gaussian_integrable_exp_lipschitz (L := L) _ r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  mgf_le r := by
    have hh := stdGaussian_mgf_lipschitz_le hf r
    change (∫ x, exp (r*(f x-∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤ _
    apply hh.trans_eq
    change exp (π^2*r^2*(L:ℝ)^2/8) = exp ((π^2*(L:ℝ)^2/4)*r^2/2)
    congr 1
    ring

lemma stdGaussian_abs_centered_moment {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hL : 0 < L) (k : ℕ) :
    (∫ x, |f x-∫ y, f y ∂stdGaussian E|^k ∂stdGaussian E) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  have hLr : 0 < (L:ℝ) := hL
  have hh := subgaussian_abs_moment (inv_pos.mpr hLr) (stdGaussian_subgaussian_lipschitz hf) k
  convert hh using 1
  have he : π^2*(L:ℝ)^2/4*((L:ℝ)⁻¹)^2/2 = π^2/8 := by field_simp [ne_of_gt hLr]; ring
  change 2*(k.factorial : ℝ)*exp (π^2/8)*(L:ℝ)^k =
    2*((k.factorial:ℝ)/(L:ℝ)⁻¹^k)*exp ((π^2*(L:ℝ)^2/4)*(L:ℝ)⁻¹^2/2)
  rw [he,inv_pow,div_inv_eq_mul]
  ring
end GaussianMoments
end SKGap

end
end
end
end
end

end OAI
