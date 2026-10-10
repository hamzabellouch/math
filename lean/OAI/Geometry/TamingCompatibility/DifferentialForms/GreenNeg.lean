import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Product

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def greenNegOne : H E F (-1) ≃ₗᵢ[ℂ] H E F 1 := reindex (-1) 1

lemma greenNegOne_distribution (u : H E F (-1)) :
    toDistribution E F 1 (greenNegOne u) = besselPotential E F (-2)
      (toDistribution E F (-1) u) := by
  have he : (-1:ℝ)-1 = -2 := by norm_num
  simpa only [greenNegOne, he] using toDistribution_reindex (-1) 1 u

lemma helmholtz_greenNegOne (u : H E F (-1)) :
    EuclideanGreen.helmholtz (toDistribution E F 1 (greenNegOne u)) =
      toDistribution E F (-1) u := by
  rw [greenNegOne_distribution]
  exact EuclideanGreen.helmholtz_green _

def weakValue : H E F (-1) →L[ℂ] H E F 0 :=
  (inclusion (E := E) (F := F) (s := 1) (t := 0) (by norm_num)).comp
    (greenNegOne (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap

def weakGradient (v : E) : H E F (-1) →L[ℂ] H E F 0 :=
  (derivative (F := F) 1 v).comp
    (greenNegOne (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap

lemma weakValue_distribution (u : H E F (-1)) :
    toDistribution E F 0 (weakValue u) = toDistribution E F 1 (greenNegOne u) := by
  exact toDistribution_inclusion (show (0:ℝ) ≤ 1 by norm_num) (greenNegOne u)

lemma weakGradient_distribution (v : E) (u : H E F (-1)) :
    toDistribution E F 0 (weakGradient v u) =
      ∂_{v} (toDistribution E F 1 (greenNegOne u)) := by
  change toDistribution E F 0 (derivative 1 v (greenNegOne u)) = _
  simpa only [toDistribution, sub_self] using
    toDistribution_derivative 1 v (greenNegOne u)

lemma weakValue_norm_le (u : H E F (-1)) : ‖weakValue u‖ ≤ ‖u‖ := by
  exact (inclusion_norm_le (E := E) (F := F) (s := 1) (t := 0)
    (by norm_num) (greenNegOne u)).trans (greenNegOne.norm_map u).le

lemma weakGradient_norm_le (v : E) (u : H E F (-1)) :
    ‖weakGradient v u‖ ≤ ‖derivative (F := F) 1 v‖ * ‖u‖ := by
  change ‖derivative (F := F) 1 v (greenNegOne u)‖ ≤ _
  simpa only [greenNegOne.norm_map] using
    ContinuousLinearMap.le_opNorm (derivative (F := F) 1 v) (greenNegOne u)

lemma product_zero_distribution (g : 𝓢(E,ℂ)) (u : H E F 0) :
    toDistribution E F 0 (product 0 g u) = smulLeftCLM F g (toDistribution E F 0 u) := by
  simpa only [toDistribution, Nat.cast_zero] using toDistribution_product 0 g u

lemma derivative_zero_distribution (v : E) (u : H E F 0) :
    toDistribution E F (-1) (derivative 0 v u) = ∂_{v} (toDistribution E F 0 u) := by
  simpa only [toDistribution, zero_sub] using toDistribution_derivative 0 v u

def negativeProductMain (g : 𝓢(E,ℂ)) : H E F (-1) →L[ℂ] H E F (-1) :=
  (inclusion (E := E) (F := F) (s := 0) (t := -1) (by norm_num)).comp
    ((product 0 g).comp weakValue)

def negativeProductTerm (g : 𝓢(E,ℂ)) (v : E) : H E F (-1) →L[ℂ] H E F (-1) :=
  (derivative (F := F) 0 v).comp ((product 0 g).comp (weakGradient v)) -
  (inclusion (E := E) (F := F) (s := 0) (t := -1) (by norm_num)).comp
    ((product 0 (∂_{v} g)).comp (weakGradient v))

lemma negativeProductMain_distribution (g : 𝓢(E,ℂ)) (u : H E F (-1)) :
    toDistribution E F (-1) (negativeProductMain g u) =
      smulLeftCLM F g (toDistribution E F 1 (greenNegOne u)) := by
  simp only [negativeProductMain, ContinuousLinearMap.comp_apply,
    toDistribution_inclusion, product_zero_distribution, weakValue_distribution]

lemma negativeProductTerm_distribution (g : 𝓢(E,ℂ)) (v : E) (u : H E F (-1)) :
    toDistribution E F (-1) (negativeProductTerm g v u) =
      smulLeftCLM F g (∂_{v} (∂_{v} (toDistribution E F 1 (greenNegOne u)))) := by
  simp only [negativeProductTerm, sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, toDistribution_inclusion, derivative_zero_distribution,
    product_zero_distribution, weakGradient_distribution,
    EuclideanSobolevOperators.distribution_derivative_product,
    add_sub_cancel_left]

def productNegOne (g : 𝓢(E,ℂ)) : H E F (-1) →L[ℂ] H E F (-1) :=
  negativeProductMain g - (((2*Real.pi)^2)⁻¹ : ℝ) •
    ∑ i : basisIndex E, negativeProductTerm g (stdOrthonormalBasis ℝ E i)

lemma toDistribution_productNegOne (g : 𝓢(E,ℂ)) (u : H E F (-1)) :
    toDistribution E F (-1) (productNegOne g u) =
      smulLeftCLM F g (toDistribution E F (-1) u) := by
  simp only [productNegOne, sub_apply, smul_apply, sum_apply, map_sub,
    ContinuousLinearMap.map_smul_of_tower, map_sum,
    negativeProductMain_distribution, negativeProductTerm_distribution]
  rw [← map_sum, ← ContinuousLinearMap.map_smul_of_tower, ← map_sub,
    ← TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  exact congrArg (smulLeftCLM F g) (helmholtz_greenNegOne u)

lemma product_zero_le_size_one (g f : 𝓢(E,ℂ))
    (hf : ‖f.toBoundedContinuousFunction‖ ≤ coefficientSize 1 g) (w : H E F 0) :
    ‖product 0 f w‖ ≤ coefficientSize 1 g * ‖w‖ :=
  (product_zero_norm_le f w).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg _))

lemma negativeProductMain_norm_le (g : 𝓢(E,ℂ)) (u : H E F (-1)) :
    ‖negativeProductMain g u‖ ≤ coefficientSize 1 g * ‖u‖ := by
  have h0 := product_zero_le_size_one g g (coefficientSize_le_succ 0 g) (weakValue u)
  have h1 := inclusion_norm_le (E := E) (F := F) (s := 0) (t := -1) (by norm_num)
    (product 0 g (weakValue u))
  exact h1.trans (h0.trans (mul_le_mul_of_nonneg_left (weakValue_norm_le u)
    (coefficientSize_nonneg _ _)))

lemma negativeProductTerm_norm_le (g : 𝓢(E,ℂ)) (i : basisIndex E) (u : H E F (-1)) :
    ‖negativeProductTerm g (stdOrthonormalBasis ℝ E i) u‖ ≤
      coefficientSize 1 g * ‖u‖ *
        ((‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖ + 1) *
          ‖derivative (F := F) 1 (stdOrthonormalBasis ℝ E i)‖) := by
  let v := stdOrthonormalBasis ℝ E i
  let w : H E F 0 := weakGradient v u
  let A := coefficientSize 1 g
  let D := ‖derivative (F := F) 0 v‖
  let D' := ‖derivative (F := F) 1 v‖
  have hw : ‖w‖ ≤ D' * ‖u‖ := weakGradient_norm_le v u
  have h1 : ‖derivative (F := F) 0 v (product 0 g w)‖ ≤ D * (A * (D' * ‖u‖)) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      ((product_zero_le_size_one g g (coefficientSize_le_succ 0 g) w).trans
        (mul_le_mul_of_nonneg_left hw (coefficientSize_nonneg _ _))) (norm_nonneg _))
  have h2 : ‖inclusion (E := E) (F := F) (s := 0) (t := -1) (by norm_num)
      (product 0 (∂_{v} g) w)‖ ≤ A * (D' * ‖u‖) :=
    (inclusion_norm_le (E := E) (F := F) (s := 0) (t := -1) (by norm_num) _).trans
      ((product_zero_le_size_one g (∂_{v} g) (coefficientSize_derivative_le 0 g i) w).trans
        (mul_le_mul_of_nonneg_left hw (coefficientSize_nonneg _ _)))
  change ‖derivative (F := F) 0 v (product 0 g w) -
    inclusion (E := E) (F := F) (s := 0) (t := -1) (by norm_num) (product 0 (∂_{v} g) w)‖ ≤ _
  exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by dsimp only [A,D,D',v]; ring))

lemma productNegOne_norm_le (g : 𝓢(E,ℂ)) (u : H E F (-1)) :
    ‖productNegOne g u‖ ≤ coefficientSize 1 g * ‖u‖ *
      (1 + |((2*Real.pi)^2)⁻¹| * ∑ i : basisIndex E,
        (‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖ + 1) *
        ‖derivative (F := F) 1 (stdOrthonormalBasis ℝ E i)‖) := by
  rw [productNegOne, sub_apply, smul_apply, sum_apply]
  apply (norm_sub_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs]
  have hterm := (norm_sum_le Finset.univ (fun i : basisIndex E =>
    negativeProductTerm (F := F) g (stdOrthonormalBasis ℝ E i) u)).trans (Finset.sum_le_sum
    (fun i _ => negativeProductTerm_norm_le g i u))
  apply (add_le_add (negativeProductMain_norm_le g u)
    (mul_le_mul_of_nonneg_left hterm (abs_nonneg _))).trans_eq
  rw [← Finset.mul_sum]
  ring

lemma productNegOne_operator_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ g : 𝓢(E,ℂ),
      ‖productNegOne (F := F) g‖ ≤ C * coefficientSize 1 g := by
  let C : ℝ := 1 + |((2*Real.pi)^2)⁻¹| * ∑ i : basisIndex E,
      (‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖ + 1) *
      ‖derivative (F := F) 1 (stdOrthonormalBasis ℝ E i)‖
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun g => (productNegOne (F := F) g).opNorm_le_bound
    (mul_nonneg hC.le (coefficientSize_nonneg _ _)) (fun u => ?_)⟩
  convert productNegOne_norm_le g u using 1
  ring

end TamingCompatibility.HilbertSobolev

end

end OAI
