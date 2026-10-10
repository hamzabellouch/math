import Mathlib
import OAI.Probability.Ballisticity.Coupling.QuenchedMoments
import OAI.Probability.Ballisticity.Estimates.SecondMomentConcentration

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma environment_absolutelyContinuous_noDropPair {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d) :
    environmentLaw ν ≪ noDropPairEnvironment ν ℓ x y := by
  apply Measure.AbsolutelyContinuous.smul_right
    (withDensity_absolutelyContinuous' ((measurable_noDropQuenched ℓ x).mul
      (measurable_noDropQuenched ℓ y)).aemeasurable ?_)
  · exact ENNReal.inv_ne_zero.mpr (ne_top_of_le_ne_top (by simp) (sharedNoDropMass_le_one ν ℓ x y))
  · filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hω
    exact mul_ne_zero (hω x).ne' (hω y).ne'

lemma norm_quenchedNoDropTest_le {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (F : Path d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ X, ‖F X‖ ≤ C) (ω : Environment d) :
    ‖quenchedNoDropTest ℓ x F ω‖ ≤ C := by
  by_cases hq : noDropQuenched ℓ x ω = 0
  · have hz : noDropQuenchedKernel ℓ x ω = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [noDropQuenchedKernel_apply _ _ _ _ MeasurableSet.univ,Set.univ_inter]
      change (noDropQuenched ℓ x ω)⁻¹*noDropQuenched ℓ x ω = 0
      simp [hq]
    simpa only [quenchedNoDropTest,hz,integral_zero_measure,norm_zero] using hC
  · let := noDropQuenchedKernel_probability ℓ x ω hq
    simpa only [quenchedNoDropTest,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := noDropQuenchedKernel ℓ x ω) (ae_of_all _ hb)

theorem actual_quenched_concentration_of_pair_moments {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x : Lattice d)
    (F : ℕ → Path d → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i X, ‖F i X‖ ≤ C) (b : ℝ)
    (hfirst : Tendsto (fun i => ∫ P, F i P.1 ∂sharedConditionedPairLaw ν ℓ x x) atTop (𝓝 b))
    (hsecond : Tendsto (fun i => ∫ P, F i P.1 * F i P.2 ∂sharedConditionedPairLaw ν ℓ x x)
      atTop (𝓝 (b^2))) :
    Tendsto (fun i => ∫ ω, (quenchedNoDropTest ℓ x (F i) ω-b)^2
      ∂noDropPairEnvironment ν ℓ x x) atTop (𝓝 0) ∧
    TendstoInMeasure (environmentLaw ν) (fun i => quenchedNoDropTest ℓ x (F i)) atTop (fun _ => b) := by
  have hp := (sharedNoDropMass_pos ν hue ℓ hℓ htrans x x).ne'
  let := noDropPairEnvironment_probability ν ℓ x x hp
  have hm := fun i => measurable_quenchedNoDropTest ℓ x (F i) (hF i)
  have hmb := fun i => norm_quenchedNoDropTest_le ℓ x (F i) C hC (hb i)
  have h1 : Tendsto (fun i => ∫ ω, quenchedNoDropTest ℓ x (F i) ω ∂noDropPairEnvironment ν ℓ x x)
      atTop (𝓝 b) := by
    simpa only [noDrop_pair_test_first_moment ν ℓ x x hp _ (hF _) C (hb _)] using hfirst
  have h2 : Tendsto (fun i => ∫ ω, (quenchedNoDropTest ℓ x (F i) ω)^2 ∂noDropPairEnvironment ν ℓ x x)
      atTop (𝓝 (b^2)) := by
    simpa only [noDrop_pair_test_second_moment ν ℓ x hp _ (hF _) C (hb _)] using hsecond
  have hl := squared_error_tendsto_of_moments (noDropPairEnvironment ν ℓ x x)
    _ hm C hmb b h1 h2
  refine ⟨hl,?_⟩
  apply tendstoInMeasure_of_absolutelyContinuous (environmentLaw ν)
    (noDropPairEnvironment ν ℓ x x) (environment_absolutelyContinuous_noDropPair ν hue ℓ hℓ htrans x x)
    _ hm b
  apply tendstoInMeasure_of_squared_error (noDropPairEnvironment ν ℓ x x) _ b _ hl
  intro i
  apply Integrable.of_bound ((hm i).sub measurable_const |>.pow_const 2).aestronglyMeasurable ((C+‖b‖)^2)
  apply ae_of_all
  intro ω
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (add_le_add (hmb i ω) (le_refl ‖b‖))

end DirectionalTransience

end

end

end OAI
