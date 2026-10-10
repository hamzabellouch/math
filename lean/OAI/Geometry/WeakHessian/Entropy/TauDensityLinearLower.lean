import Mathlib
import OAI.Geometry.WeakHessian.Entropy.AcBoundedRenyiGaps
import OAI.Geometry.WeakHessian.LocalBounds.SigmaCoeffExpLower

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
open MeasureTheory
open scoped ENNReal

lemma tau_density_linear_lower {K N s θ : ℝ} (hN : 1 < N)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hθ : 0 ≤ θ) {r : ℝ≥0∞} (hr : 0 < r) (hrt : r ≠ ∞) :
    ENNReal.ofReal (s*r.toReal^(-1/N) + (1/N)*(K*s*(1-s^2)/6)*(θ^2*r.toReal^(-1/N))) ≤
      tauCoeff K N s θ * r^(-1/N) := by
  have hrp : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrt
  have he : ENNReal.ofReal (r.toReal^(-1/N)) = r^(-1/N) := by
    rw [← ENNReal.ofReal_rpow_of_pos hrp,ENNReal.ofReal_toReal hrt]
  have H := mul_le_mul_left (tauCoeff_exp_lower (K := K) hN hs hs1 hθ) (r^(-1/N))
  apply le_trans _ H
  rw [← he,← ENNReal.ofReal_mul (mul_nonneg hs (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  have Hexp := Real.add_one_le_exp (K*θ^2*(1-s^2)/(6*N))
  have HH := mul_le_mul_of_nonneg_left Hexp (mul_nonneg hs (Real.rpow_nonneg hrp.le (-1/N)))
  exact le_trans (le_of_eq (by field_simp; ring)) (le_trans HH (le_of_eq (by ring)))

lemma integral_le_of_lintegral_ofReal_le {Y : Type*} [MeasurableSpace Y]
    {π : Measure Y} [IsFiniteMeasure π] {f : Y → ℝ} (hi : Integrable f π)
    {R : ℝ} (hR : 0 ≤ R) (h : (∫⁻ y, ENNReal.ofReal (f y) ∂π) ≤ ENNReal.ofReal R) :
    (∫ y, f y ∂π) ≤ R := by
  have hp : Integrable (fun y => max (f y) 0) π := hi.pos_part
  have H : ENNReal.ofReal (∫ y, max (f y) 0 ∂π) ≤ ENNReal.ofReal R := by
    rw [ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall fun y => le_max_right _ _)]
    have hmax : ∀ y, ENNReal.ofReal (max (f y) 0) = ENNReal.ofReal (f y) := by
      intro y
      rw [ENNReal.ofReal_max,ENNReal.ofReal_zero]
      exact max_eq_left bot_le
    simpa only [hmax] using h
  exact (integral_mono hi hp (fun y => le_max_left _ _)).trans
    ((ENNReal.ofReal_le_ofReal_iff hR).mp H)
end WeakHessian

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma renyiIntegral_ofReal {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {N : ℝ} (hN : 1 < N) :
    renyiIntegral m μ N = ENNReal.ofReal (∫ x, (μ.rnDeriv m x).toReal^(1-1/N) ∂m) := by
  have ha : 0 ≤ 1/N := by positivity
  have ha1 : 1/N < 1 := (div_lt_one (by linarith : 0<N)).mpr hN
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_rpow_sub Measure.integrable_toReal_rnDeriv
      (Eventually.of_forall fun x => ENNReal.toReal_nonneg) ha ha1)
    (Eventually.of_forall fun x => Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top μ m] with x hx
  rw [ENNReal.toReal_rpow,ENNReal.ofReal_toReal
    (ENNReal.rpow_ne_top_of_nonneg (by linarith : 0 ≤ 1-1/N) hx.ne)]

lemma integrable_density_neg_rpow_comp {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {π : Measure Y} (hac : μ ≪ m) {e : Y → X} (he : Measurable e)
    (hmap : Measure.map e π = μ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Integrable (fun y => (μ.rnDeriv m (e y)).toReal^(-a)) π := by
  have H : Integrable (fun x => (μ.rnDeriv m x).toReal^(-a)) (Measure.map e π) := by
    simpa only [hmap] using integrable_density_neg_rpow hac ha ha1
  exact H.comp_measurable he

lemma integral_density_neg_rpow_comp {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]
    {π : Measure Y} (hac : μ ≪ m) {e : Y → X} (he : Measurable e)
    (hmap : Measure.map e π = μ) {a : ℝ} (ha : a < 1) :
    (∫ y, (μ.rnDeriv m (e y)).toReal^(-a) ∂π) =
      ∫ x, (μ.rnDeriv m x).toReal^(1-a) ∂m := by
  have H := integral_map (μ := π) he.aemeasurable
    (((Measure.measurable_rnDeriv μ m).ennreal_toReal.pow_const (-a)).aestronglyMeasurable)
  rw [hmap] at H
  exact H.symm.trans (integral_density_neg_rpow hac ha)

lemma cd_renyi_gap_bound {m μ₀ μ₁ μt : Measure X} [IsFiniteMeasure m]
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μt]
    {π : Measure Y} [IsProbabilityMeasure π] {e₀ e₁ : Y → X}
    (he₀ : Measurable e₀) (he₁ : Measurable e₁)
    (hm₀ : Measure.map e₀ π = μ₀) (hm₁ : Measure.map e₁ π = μ₁)
    (hac₀ : μ₀ ≪ m) (hac₁ : μ₁ ≪ m)
    {θ : Y → ℝ} (hθ : Measurable θ) (hθ0 : ∀ᵐ y ∂π, 0 ≤ θ y)
    {C : ℝ} (hb : ∀ᵐ y ∂π, θ y ^ 2 ≤ C) {K N t : ℝ}
    (hN : 1 < N) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hcd : (∫⁻ y, tauCoeff K N (1-t) (θ y)*(μ₀.rnDeriv m (e₀ y))^(-1/N) +
      tauCoeff K N t (θ y)*(μ₁.rnDeriv m (e₁ y))^(-1/N) ∂π) ≤ renyiIntegral m μt N) :
    (1-∫ x, (μt.rnDeriv m x).toReal^(1-1/N) ∂m)/(1/N) ≤
      (1-t)*((1-∫ x, (μ₀.rnDeriv m x).toReal^(1-1/N) ∂m)/(1/N)) +
      t*((1-∫ x, (μ₁.rnDeriv m x).toReal^(1-1/N) ∂m)/(1/N)) -
      K*(1-t)*(1-(1-t)^2)/6*(∫ y, θ y^2*(μ₀.rnDeriv m (e₀ y)).toReal^(-1/N) ∂π) -
      K*t*(1-t^2)/6*(∫ y, θ y^2*(μ₁.rnDeriv m (e₁ y)).toReal^(-1/N) ∂π) := by
  have ha : 0 < 1/N := by positivity
  have ha1 : 1/N < 1 := (div_lt_one (by linarith : 0<N)).mpr hN
  have heq : -(1/N) = -1/N := by ring
  have hi₀ := integrable_density_neg_rpow_comp hac₀ he₀ hm₀ ha.le ha1
  have hi₁ := integrable_density_neg_rpow_comp hac₁ he₁ hm₁ ha.le ha1
  rw [heq] at hi₀ hi₁
  have hθb : ∀ᵐ y ∂π, ‖θ y^2‖ ≤ C := hb.mono fun y hy => by
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hc₀ := hi₀.bdd_mul (hθ.pow_const 2).aestronglyMeasurable hθb
  have hc₁ := hi₁.bdd_mul (hθ.pow_const 2).aestronglyMeasurable hθb
  let f : Y → ℝ := fun y =>
    (1-t)*(μ₀.rnDeriv m (e₀ y)).toReal^(-1/N) +
      (1/N)*(K*(1-t)*(1-(1-t)^2)/6)*(θ y^2*(μ₀.rnDeriv m (e₀ y)).toReal^(-1/N)) +
    (t*(μ₁.rnDeriv m (e₁ y)).toReal^(-1/N) +
      (1/N)*(K*t*(1-t^2)/6)*(θ y^2*(μ₁.rnDeriv m (e₁ y)).toReal^(-1/N)))
  have hfi : Integrable f π :=
    ((hi₀.const_mul _).add (hc₀.const_mul _)).add ((hi₁.const_mul _).add (hc₁.const_mul _))
  have hp₀ : ∀ᵐ y ∂π, 0 < μ₀.rnDeriv m (e₀ y) ∧ μ₀.rnDeriv m (e₀ y) ≠ ∞ := by
    have H : ∀ᵐ x ∂Measure.map e₀ π, 0 < μ₀.rnDeriv m x ∧ μ₀.rnDeriv m x ≠ ∞ := by
      rw [hm₀]
      filter_upwards [Measure.rnDeriv_pos hac₀, hac₀.ae_le (Measure.rnDeriv_lt_top μ₀ m)] with x hp ht
      exact ⟨hp,ht.ne⟩
    exact ae_of_ae_map he₀.aemeasurable H
  have hp₁ : ∀ᵐ y ∂π, 0 < μ₁.rnDeriv m (e₁ y) ∧ μ₁.rnDeriv m (e₁ y) ≠ ∞ := by
    have H : ∀ᵐ x ∂Measure.map e₁ π, 0 < μ₁.rnDeriv m x ∧ μ₁.rnDeriv m x ≠ ∞ := by
      rw [hm₁]
      filter_upwards [Measure.rnDeriv_pos hac₁, hac₁.ae_le (Measure.rnDeriv_lt_top μ₁ m)] with x hp ht
      exact ⟨hp,ht.ne⟩
    exact ae_of_ae_map he₁.aemeasurable H
  have H : (∫ y, f y ∂π) ≤ ∫ x, (μt.rnDeriv m x).toReal^(1-1/N) ∂m := by
    apply integral_le_of_lintegral_ofReal_le hfi
      (integral_nonneg fun x => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    rw [← renyiIntegral_ofReal hN]
    apply le_trans (lintegral_mono_ae ?_) hcd
    filter_upwards [hp₀,hp₁,hθ0] with y hy₀ hy₁ hyθ
    exact ENNReal.ofReal_add_le.trans (add_le_add
      (tau_density_linear_lower (K := K) hN (by linarith) (by linarith) hyθ hy₀.1 hy₀.2)
      (tau_density_linear_lower (K := K) hN ht ht1 hyθ hy₁.1 hy₁.2))
  have H₀ := integral_density_neg_rpow_comp hac₀ he₀ hm₀ ha1
  have H₁ := integral_density_neg_rpow_comp hac₁ he₁ hm₁ ha1
  rw [heq] at H₀ H₁
  dsimp only [f] at H
  have HS := integral_add
    ((hi₀.const_mul (1-t)).add (hc₀.const_mul ((1/N)*(K*(1-t)*(1-(1-t)^2)/6))))
    ((hi₁.const_mul t).add (hc₁.const_mul ((1/N)*(K*t*(1-t^2)/6))))
  have HS₀ := integral_add (hi₀.const_mul (1-t)) (hc₀.const_mul ((1/N)*(K*(1-t)*(1-(1-t)^2)/6)))
  have HS₁ := integral_add (hi₁.const_mul t) (hc₁.const_mul ((1/N)*(K*t*(1-t^2)/6)))
  simp only [Pi.add_apply] at HS HS₀ HS₁
  rw [HS,HS₀,HS₁] at H
  simp only [integral_const_mul,H₀,H₁] at H
  apply (div_le_iff₀ ha).mpr
  field_simp at H ⊢
  nlinarith
end WeakHessian

end
end InlinedFile0

end OAI
