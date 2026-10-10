import OAI.Analysis.IrrationalRotation.Model.ProductBase
import OAI.Analysis.IrrationalRotation.Product.ProductCocycle
import OAI.Analysis.IrrationalRotation.Analysis.ExtendedExponential

namespace OAI

open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

theorem cost_summand_nonneg (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base) (i : ℕ) :
    0 ≤ c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) := by
  apply mul_nonneg (hc i)
  have hf : (0 : ℤ) ≤ ⌊circleRepresentative (x i) + θ i⌋ := by
    apply Int.floor_nonneg.mpr
    exact add_nonneg (ProductCocycle.representative_mem_Ico (x i)).1 (hθ i)
  exact_mod_cast hf

theorem logarithmicCost_eq_ofReal_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    logarithmicCost θ c x =
      ENNReal.ofReal (∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (cost_summand_nonneg θ c hθ hc x)
    (FiniteSupportCocycle.summable_weighted_int c hx)).symm

theorem weight_eq_cocycleVersion_of_finite_support (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    weight θ c x = ProductCocycle.cocycleVersion θ c 1 x := by
  have hnonneg : 0 ≤ ∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) :=
    tsum_nonneg (cost_summand_nonneg θ c hθ hc x)
  unfold weight
  rw [logarithmicCost_eq_ofReal_tsum θ c hθ hc x hx,
    EReal.coe_ennreal_ofReal, max_eq_left hnonneg, ← EReal.coe_neg,
    EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [ProductCocycle.cocycleVersion, Int.cast_one, one_mul,
    circleRepresentative, ProductCocycle.representative]

theorem negLogCost_weight (θ c : ℕ → ℝ) (x : Base) :
    negLogCost (weight θ c x) = logarithmicCost θ c x :=
  negLogCost_extendedExpNeg _

theorem weight_mem_Icc (θ c : ℕ → ℝ) (x : Base) :
    weight θ c x ∈ Icc (0 : ℝ) 1 :=
  extendedExpNeg_mem_Icc _

theorem measurable_logarithmicCost (θ c : ℕ → ℝ) :
    Measurable (logarithmicCost θ c) := by
  apply Measurable.tsum
  intro i
  have hrep : Measurable (fun x : Base ↦ circleRepresentative (x i)) :=
    ProductCocycle.measurable_representative.comp (measurable_pi_apply i)
  exact (measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const (θ i)).floor))).ennreal_ofReal

theorem measurable_weight (θ c : ℕ → ℝ) : Measurable (weight θ c) := by
  exact (((measurable_coe_ennreal_ereal.comp
    (measurable_logarithmicCost θ c)).neg).ereal_exp).ennreal_toReal

theorem weight_ae_eq_cocycleVersion (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    weight θ c =ᵐ[baseMeasure] ProductCocycle.cocycleVersion θ c 1 := by
  have hall := CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  filter_upwards [hall] with x hx
  apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc x
  simpa only [HasFiniteSupport, circleRepresentative, Int.cast_one, one_mul] using hx 1

theorem ae_weight_pos (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, 0 < weight θ c x := by
  filter_upwards [weight_ae_eq_cocycleVersion θ c hθ0 hc hθ] with x hx
  rw [hx]
  exact ProductCocycle.cocycleVersion_pos θ c 1 x

theorem weight_eq_zero_iff (θ c : ℕ → ℝ) (x : Base) :
    weight θ c x = 0 ↔ logarithmicCost θ c x = ∞ :=
  extendedExpNeg_eq_zero_iff _

theorem ae_exists_finset_weight (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, ∃ s : Finset ℕ, weight θ c x = Real.exp (-∑ i ∈ s, c i) := by
  filter_upwards [weight_ae_eq_cocycleVersion θ c (fun i ↦ (hθ01 i).1) hc hθ,
    ProductCocycle.ae_exists_finset_cocycleVersion_one θ c hθ01 hθ] with x hx hfin
  simpa only [hx] using hfin

theorem lintegral_negLogCost_weight (θ c : ℕ → ℝ) :
    (∫⁻ x, negLogCost (weight θ c x) ∂baseMeasure) =
      ∫⁻ x, logarithmicCost θ c x ∂baseMeasure := by
  simp only [negLogCost_weight]

theorem hasNegInfiniteLogIntegral_iff (θ c : ℕ → ℝ) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ c) ↔
      (∫⁻ x, logarithmicCost θ c x ∂baseMeasure) = ∞ := by
  rw [HasNegInfiniteLogIntegral, lintegral_negLogCost_weight]

end Invariant233.ProductModel

end OAI
