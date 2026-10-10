import OAI.Analysis.Unitarizability.Average
import OAI.Analysis.Unitarizability.Model
import Mathlib.Analysis.Normed.Module.WeakDual

namespace OAI

/-! Vector means and their translation error bounds. -/
noncomputable section
namespace Dixmier
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G]

omit [Group G] [TopologicalSpace G] in
theorem summable_l2_sq (ξ : ScalarL2 G) : Summable (fun x => ‖ξ x‖ ^ 2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num)

def vectorMeanValue (ξ : ScalarL2 G) (b : G →ᵇ ℂ) : ℂ :=
  ∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)

theorem vectorMean_summable (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    Summable (fun x => (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹) : G → ℂ) := by
  apply Summable.of_norm_bounded ((summable_l2_sq ξ).mul_right ‖b‖)
  intro x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ x‖)]
  exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (sq_nonneg _)

theorem vectorMean_norm_le (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    ‖vectorMeanValue ξ b‖ ≤ ‖ξ‖ ^ 2 * ‖b‖ := by
  have hb : ∀ x, ‖(‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)‖ ≤ ‖ξ x‖ ^ 2 * ‖b‖ := by
    intro x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ x‖)]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (sq_nonneg _)
  calc
    ‖vectorMeanValue ξ b‖ ≤ ∑' x, ‖(‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)‖ :=
      norm_tsum_le_tsum_norm (vectorMean_summable ξ b).norm
    _ ≤ ∑' x, ‖ξ x‖ ^ 2 * ‖b‖ :=
      Summable.tsum_le_tsum hb (vectorMean_summable ξ b).norm ((summable_l2_sq ξ).mul_right ‖b‖)
    _ = ‖ξ‖ ^ 2 * ‖b‖ := by rw [tsum_mul_right, ← l2_norm_sq]

def vectorMeanLinear (ξ : ScalarL2 G) : (G →ᵇ ℂ) →ₗ[ℂ] ℂ where
  toFun := vectorMeanValue ξ
  map_add' b c := by
    simp only [vectorMeanValue, BoundedContinuousFunction.add_apply, mul_add]
    exact (vectorMean_summable ξ b).tsum_add (vectorMean_summable ξ c)
  map_smul' z b := by
    simp only [vectorMeanValue, BoundedContinuousFunction.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm _ z, mul_assoc]
    exact tsum_mul_left

def vectorMean (ξ : ScalarL2 G) : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  (vectorMeanLinear ξ).mkContinuous (‖ξ‖ ^ 2) (vectorMean_norm_le ξ)

@[simp] theorem vectorMean_apply (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    vectorMean ξ b = vectorMeanValue ξ b := rfl

theorem vectorMean_one (ξ : ScalarL2 G) :
    vectorMean ξ (BoundedContinuousFunction.const G 1) = (‖ξ‖ ^ 2 : ℝ) := by
  simp only [vectorMean_apply, vectorMeanValue, BoundedContinuousFunction.const_apply, mul_one]
  rw [← Complex.ofReal_tsum, ← l2_norm_sq]

theorem vectorMean_opNorm_le (ξ : ScalarL2 G) : ‖vectorMean ξ‖ ≤ ‖ξ‖ ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) (vectorMean_norm_le ξ)

theorem vectorMean_positive (ξ : ScalarL2 G) (b : G →ᵇ ℂ)
    (hb : ∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) :
    0 ≤ (vectorMean ξ b).re ∧ (vectorMean ξ b).im = 0 := by
  change 0 ≤ (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)).re ∧
    (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)).im = 0
  rw [Complex.re_tsum (vectorMean_summable ξ b), Complex.im_tsum (vectorMean_summable ξ b)]
  constructor
  · apply tsum_nonneg
    intro x
    simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using mul_nonneg (sq_nonneg ‖ξ x‖) (hb x⁻¹).1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, fun x => (hb x).2, mul_zero, tsum_zero]

theorem vectorMean_translate [DiscreteTopology G] (ξ : ScalarL2 G) (g : G) (b : G →ᵇ ℂ) :
    vectorMean ξ (leftTranslate g b) = vectorMean (rightRegular g⁻¹ ξ) b := by
  change (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (g⁻¹ * x⁻¹)) =
    ∑' x, (‖ξ (x * g⁻¹)‖ ^ 2 : ℝ) * b x⁻¹
  rw [← (Equiv.mulRight g).tsum_eq (fun x => (‖ξ (x * g⁻¹)‖ ^ 2 : ℝ) * b x⁻¹)]
  simp [mul_assoc]

theorem norm_sq_difference_le (a b : ℂ) :
    |‖a‖^2 - ‖b‖^2| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have he : |‖a‖^2 - ‖b‖^2| = |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) := by
    conv_rhs => rw [← abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
    rw [← abs_mul]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b)
    (add_nonneg (norm_nonneg a) (norm_nonneg b))

omit [Group G] [TopologicalSpace G] in
/-- The l2-to-l1 estimate behind the vector-mean translation error bound. -/
theorem l2_square_difference_bound (ξ η : ScalarL2 G) :
    Summable (fun x => |‖ξ x‖^2 - ‖η x‖^2|) ∧
    (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) := by
  have hp : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    norm_num [Real.HolderConjugate]
    constructor <;> norm_num
  have h1 := lp.tsum_mul_le_mul_norm hp (ξ - η) ξ
  have h2 := lp.tsum_mul_le_mul_norm hp (ξ - η) η
  have hsum := h1.1.add h2.1
  have hb : ∀ x, |‖ξ x‖^2 - ‖η x‖^2| ≤ ‖(ξ - η) x‖ * ‖ξ x‖ + ‖(ξ - η) x‖ * ‖η x‖ := by
    intro x
    simpa [mul_add] using norm_sq_difference_le (ξ x) (η x)
  have hs := Summable.of_nonneg_of_le (fun x => abs_nonneg _) hb hsum
  refine ⟨hs, ?_⟩
  calc
    (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) ≤ ∑' x, (‖(ξ - η) x‖ * ‖ξ x‖ + ‖(ξ - η) x‖ * ‖η x‖) :=
      Summable.tsum_le_tsum hb hs hsum
    _ = (∑' x, ‖(ξ - η) x‖ * ‖ξ x‖) + ∑' x, ‖(ξ - η) x‖ * ‖η x‖ := h1.1.tsum_add h2.1
    _ ≤ ‖ξ - η‖ * ‖ξ‖ + ‖ξ - η‖ * ‖η‖ := add_le_add h1.2 h2.2
    _ = ‖ξ - η‖ * (‖ξ‖ + ‖η‖) := (mul_add _ _ _).symm

theorem vectorMean_difference_bound (ξ η : ScalarL2 G) (b : G →ᵇ ℂ) :
    ‖vectorMean ξ b - vectorMean η b‖ ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) * ‖b‖ := by
  let f : G → ℂ := fun x => ((‖ξ x‖^2 - ‖η x‖^2 : ℝ) : ℂ) * b x⁻¹
  have hf : Summable f := ((vectorMean_summable ξ b).sub (vectorMean_summable η b)).congr
    (fun x => by dsimp [f]; push_cast; ring)
  have he : vectorMean ξ b - vectorMean η b = ∑' x, f x := by
    rw [vectorMean_apply, vectorMean_apply, vectorMeanValue, vectorMeanValue,
      ← (vectorMean_summable ξ b).tsum_sub (vectorMean_summable η b)]
    apply tsum_congr
    intro x
    dsimp [f]
    push_cast
    ring
  have hsq := l2_square_difference_bound ξ η
  have hb : ∀ x, ‖f x‖ ≤ |‖ξ x‖^2 - ‖η x‖^2| * ‖b‖ := by
    intro x
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (abs_nonneg _)
  rw [he]
  calc
    ‖∑' x, f x‖ ≤ ∑' x, ‖f x‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' x, |‖ξ x‖^2 - ‖η x‖^2| * ‖b‖ :=
      Summable.tsum_le_tsum hb hf.norm (hsq.1.mul_right ‖b‖)
    _ = (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) * ‖b‖ := tsum_mul_right
    _ ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) * ‖b‖ := mul_le_mul_of_nonneg_right hsq.2 (norm_nonneg _)

/-- The vector-mean translation error estimate. -/
theorem vectorMean_translation_bound [DiscreteTopology G] (ξ : ScalarL2 G) (hξ : ‖ξ‖ = 1)
    (g : G) (b : G →ᵇ ℂ) :
    ‖vectorMean ξ (leftTranslate g b) - vectorMean ξ b‖ ≤
      2 * ‖b‖ * ‖rightRegular g⁻¹ ξ - ξ‖ := by
  rw [vectorMean_translate]
  have h := vectorMean_difference_bound (rightRegular g⁻¹ ξ) ξ b
  rw [rightRegular_norm_map, hξ] at h
  nlinarith

end Dixmier

end

end OAI
