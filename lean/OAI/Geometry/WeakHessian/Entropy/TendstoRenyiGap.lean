import Mathlib
import OAI.Geometry.WeakHessian.Entropy.TauDensityLinearLower

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma tendsto_renyi_gap {m μ : Measure X} [IsFiniteMeasure m] [IsProbabilityMeasure μ]
    (hE : FiniteEntropy m μ) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1) (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => (1-∫ x, (μ.rnDeriv m x).toReal^(1-a n) ∂m)/(a n))
      atTop (𝓝 (entropyReal m μ)) := by
  have hi : Integrable (fun x => (μ.rnDeriv m x).toReal) m := Measure.integrable_toReal_rnDeriv
  have hn : ∀ᵐ x ∂m, 0 ≤ (μ.rnDeriv m x).toReal := Eventually.of_forall fun x => ENNReal.toReal_nonneg
  have H := tendsto_integral_renyiKernel hi hn
    ((integrable_klFun_rnDeriv_iff hE.1).mpr hE.2) ha ha1 halim
  have heq : ∀ n, (∫ x, renyiKernel (a n) (μ.rnDeriv m x).toReal ∂m) =
      (1-∫ x, (μ.rnDeriv m x).toReal^(1-a n) ∂m)/(a n) + m.real Set.univ-1 := by
    intro n
    simp only [renyiKernel]
    rw [integral_sub,integral_add,integral_div,integral_sub,
      Measure.integral_toReal_rnDeriv hE.1,probReal_univ (μ := μ),integral_const,smul_eq_mul,mul_one]
    · exact hi
    · exact integrable_rpow_sub hi hn (ha n).le (ha1 n)
    · exact (hi.sub (integrable_rpow_sub hi hn (ha n).le (ha1 n))).div_const _
    · exact integrable_const 1
    · exact ((hi.sub (integrable_rpow_sub hi hn (ha n).le (ha1 n))).div_const _).add (integrable_const 1)
    · exact hi
  simp only [heq] at H
  rw [integral_klFun_rnDeriv hE.1 hE.2,probReal_univ (μ := μ)] at H
  have HH := (H.sub_const (m.real Set.univ)).add_const 1
  have alg : ∀ x y : ℝ, x+y-1-y+1 = x := by intros; ring
  simpa only [alg,entropyReal] using HH

lemma cd_entropy_bound_of_dimensions {m μ₀ μ₁ μt : Measure X} [IsFiniteMeasure m]
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μt]
    {π : Measure Y} [IsProbabilityMeasure π] {e₀ e₁ : Y → X}
    (he₀ : Measurable e₀) (he₁ : Measurable e₁)
    (hm₀ : Measure.map e₀ π = μ₀) (hm₁ : Measure.map e₁ π = μ₁)
    (hE₀ : FiniteEntropy m μ₀) (hE₁ : FiniteEntropy m μ₁)
    {θ : Y → ℝ} (hθ : Measurable θ) (hθ0 : ∀ᵐ y ∂π, 0 ≤ θ y)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ y ∂π, θ y ^ 2 ≤ C) {K t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) {d : ℕ → ℝ} (hd : ∀ n, 1 < d n)
    (hdlim : Tendsto (fun n => 1/d n) atTop (𝓝 0))
    (hcd : ∀ n, (∫⁻ y, tauCoeff K (d n) (1-t) (θ y)*(μ₀.rnDeriv m (e₀ y))^(-1/(d n)) +
      tauCoeff K (d n) t (θ y)*(μ₁.rnDeriv m (e₁ y))^(-1/(d n)) ∂π) ≤ renyiIntegral m μt (d n)) :
    FiniteEntropy m μt ∧ entropyReal m μt ≤ (1-t)*entropyReal m μ₀+t*entropyReal m μ₁ -
      K/2*t*(1-t)*(∫ y, θ y^2 ∂π) := by
  have ha : ∀ n, 0 < 1/d n := fun n => one_div_pos.mpr (lt_trans zero_lt_one (hd n))
  have ha1 : ∀ n, 1/d n < 1 := fun n => (div_lt_one (lt_trans zero_lt_one (hd n))).mpr (hd n)
  have HL₀ := tendsto_renyi_gap hE₀ ha ha1 hdlim
  have HL₁ := tendsto_renyi_gap hE₁ ha ha1 hdlim
  have hψ : AEStronglyMeasurable (fun y => θ y^2) π := (hθ.pow_const 2).aestronglyMeasurable
  have hb' : ∀ᵐ y ∂π, |θ y^2| ≤ C := hb.mono fun y hy => by rwa [abs_of_nonneg (sq_nonneg _)]
  have HC₀ := tendsto_integral_weighted_density_neg_rpow hE₀.1 he₀ hm₀ hψ hC hb'
    (fun n => (ha n).le) (fun n => (ha1 n).le) hdlim
  have HC₁ := tendsto_integral_weighted_density_neg_rpow hE₁.1 he₁ hm₁ hψ hC hb'
    (fun n => (ha n).le) (fun n => (ha1 n).le) hdlim
  simp only [← neg_div] at HC₀ HC₁
  have HL := (((HL₀.const_mul (1-t)).add (HL₁.const_mul t)).sub
    (HC₀.const_mul (K*(1-t)*(1-(1-t)^2)/6))).sub (HC₁.const_mul (K*t*(1-t^2)/6))
  have HE := finiteEntropy_of_renyi_gaps ha ha1 hdlim HL
    (fun n => cd_renyi_gap_bound he₀ he₁ hm₀ hm₁ hE₀.1 hE₁.1 hθ hθ0 hb (hd n) ht ht1 (hcd n))
  refine ⟨HE.1,HE.2.trans_eq ?_⟩
  ring
end WeakHessian

end
end InlinedFile0

end OAI
