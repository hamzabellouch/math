import Mathlib
import OAI.Probability.SphericalField.Sphere.Polar

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma canonicalField_band_bounds (n : ℕ) (b ε : ℝ)
    (ρ : Measure (Spin (n+1))) [SFinite ρ] :
    angularFieldFactor ρ (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))) *
      canonicalRadialMass n b (normSquareBand n ε) ≤
        (∫⁻ x in normSquareBand n ε, linearFieldFactor ρ x ∂canonicalRadialMass n b) ∧
    (∫⁻ x in normSquareBand n ε, linearFieldFactor ρ x ∂canonicalRadialMass n b) ≤
      angularFieldFactor ρ (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))) *
        canonicalRadialMass n b (normSquareBand n ε) := by
  have hh := polar_weighted_bounds (volume : Measure (RadialSpace n))
    (linearFieldFactor ρ) (linearFieldFactor_measurable ρ)
    (canonicalBandRadiusWeight n b ε) (canonicalBandRadiusWeight_measurable n b ε)
    (L := angularFieldFactor ρ (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))))
    (U := angularFieldFactor ρ (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))))
  rw [canonicalBandRadiusWeight_integral n b ε _ (linearFieldFactor_measurable ρ),
    canonicalBandRadiusWeight_mass] at hh
  apply hh
  · intro r hr
    have hb : ((n+1:ℕ):ℝ)*(1-ε) ≤ (r:ℝ)^2 ∧ (r:ℝ)^2 ≤ ((n+1:ℕ):ℝ)*(1+ε) := by
      by_contra hn
      exact hr (by simp only [canonicalBandRadiusWeight,Set.indicator_apply,Set.mem_ofPred_eq,hn,ite_false])
    change angularFieldFactor ρ _ ≤ angularFieldFactor ρ (r:ℝ)
    apply angularFieldFactor_mono ρ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff).mpr ⟨r.property.le,hb.1⟩
  · intro r hr
    have hb : ((n+1:ℕ):ℝ)*(1-ε) ≤ (r:ℝ)^2 ∧ (r:ℝ)^2 ≤ ((n+1:ℕ):ℝ)*(1+ε) := by
      by_contra hn
      exact hr (by simp only [canonicalBandRadiusWeight,Set.indicator_apply,Set.mem_ofPred_eq,hn,ite_false])
    change angularFieldFactor ρ (r:ℝ) ≤ angularFieldFactor ρ _
    apply angularFieldFactor_mono ρ r.property.le
    exact (Real.le_sqrt' r.property).mpr hb.2

lemma canonicalWeighted_mass_le (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) {a b c : ℝ}
    (hc : ∀ x ∈ A, -(a/2)*‖x‖^2 ≤ c-(b/2)*‖x‖^2) :
    (∫⁻ x in A, F x ∂canonicalRadialMass n a) ≤
      ENNReal.ofReal (Real.exp c) * (∫⁻ x, F x ∂canonicalRadialMass n b) := by
  have hd (d : ℝ) : Measurable (fun x : RadialSpace n => ENNReal.ofReal (canonicalRadialDensity n d x)) :=
    (canonicalRadialDensity_continuous n d).measurable.ennreal_ofReal
  rw [canonicalRadialMass,setLIntegral_withDensity_eq_setLIntegral_mul _ (hd a) hF hA,
    canonicalRadialMass,lintegral_withDensity_eq_lintegral_mul _ (hd b) hF,
    ← lintegral_const_mul _ ((hd b).mul hF)]
  calc
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp c) *
        (ENNReal.ofReal (canonicalRadialDensity n b x) * F x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      change ENNReal.ofReal (canonicalRadialDensity n a x) * F x ≤ _
      rw [← mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos c).le]
      apply mul_le_mul (ENNReal.ofReal_le_ofReal ?_) le_rfl (by positivity) (by positivity)
      unfold canonicalRadialDensity
      calc
        _ ≤ radialNormalizer n * Real.exp (c-(b/2)*‖x‖^2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hc x hx)) (radialNormalizer_pos n).le
        _ = _ := by rw [Real.exp_sub,neg_mul,Real.exp_neg]; ring
    _ ≤ _ := setLIntegral_le_lintegral _ _

lemma canonicalWeighted_upper_tail (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    (b ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ x in {x : RadialSpace n | ((n+1:ℕ):ℝ)*(1+ε) ≤ ‖x‖^2}, F x ∂canonicalRadialMass n b) ≤
      ENNReal.ofReal (Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b-δ)) := by
  apply canonicalWeighted_mass_le n F hF
    (measurableSet_le measurable_const (continuous_norm.pow 2).measurable)
  intro x hx
  dsimp only [Set.mem_ofPred_eq,Pi.pow_apply] at hx
  have := mul_le_mul_of_nonneg_left hx hδ
  nlinarith

lemma canonicalWeighted_lower_tail (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    (b ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ x in {x : RadialSpace n | ‖x‖^2 ≤ ((n+1:ℕ):ℝ)*(1-ε)}, F x ∂canonicalRadialMass n b) ≤
      ENNReal.ofReal (Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b+δ)) := by
  apply canonicalWeighted_mass_le n F hF
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const)
  intro x hx
  dsimp only [Set.mem_ofPred_eq,Pi.pow_apply] at hx
  have := mul_le_mul_of_nonneg_left hx hδ
  nlinarith

end SphericalPerceptron
end
end
end

end OAI
