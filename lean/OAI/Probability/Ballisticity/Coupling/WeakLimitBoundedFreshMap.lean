import Mathlib
import OAI.Probability.Ballisticity.Estimates.WeightedConditioned

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weak_limit_of_bounded_fresh_map {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : ℕ → Measure Ω)
    [∀ i, IsProbabilityMeasure (η i)] (S : Ω → Ω) (hS : Measurable S)
    (hmap : ∀ i, (η i).map S = μ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hdom : ∀ i, η i ≤ C • μ) (F : ℕ → Ω → E) (hF : ∀ i, Measurable (F i))
    (W : ProbabilityMeasure E)
    (hlim : Tendsto (fun i => ProbabilityMeasure.map (⟨μ,inferInstance⟩ : ProbabilityMeasure Ω)
      (F i)) atTop (𝓝 W))
    (hclose : ∀ ε, 0 < ε → Tendsto (fun i => μ.real
      {ω | ε ≤ dist (F i (S ω)) (F i ω)}) atTop (𝓝 0)) :
    Tendsto (fun i => ProbabilityMeasure.map (⟨η i,inferInstance⟩ : ProbabilityMeasure Ω)
      (F i)) atTop (𝓝 W) := by
  apply weak_map_of_varying_close η (fun i => F i ∘ S) F
    (fun i => (hF i).comp hS) hF W
  · have he (i : ℕ) : ProbabilityMeasure.map (⟨η i,inferInstance⟩ : ProbabilityMeasure Ω)
        (F i ∘ S) =
        ProbabilityMeasure.map (⟨μ,inferInstance⟩ : ProbabilityMeasure Ω) (F i) := by
      apply Subtype.ext
      change (η i).map (F i ∘ S) = μ.map (F i)
      rw [← Measure.map_map (hF i) hS,hmap]
    simpa only [he] using hlim
  · intro ε hε
    have hb (i : ℕ) : (η i).real {ω | ε ≤ dist (F i (S ω)) (F i ω)} ≤
        C.toReal * μ.real {ω | ε ≤ dist (F i (S ω)) (F i ω)} := by
      have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top hC (measure_ne_top _ _)) (hdom i {ω | ε ≤ dist (F i (S ω)) (F i ω)})
      simpa only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,Measure.real] using hh
    exact squeeze_zero (fun _ => measureReal_nonneg) hb
      (by simpa only [mul_zero] using (hclose ε hε).const_mul C.toReal)

lemma weightedConditioned_finite {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    [IsProbabilityMeasure (conditionedLaw ν ℓ)] (g : Environment d → ℝ≥0∞)
    (hg : Measurable g) (hgle : ∀ ω, g ω ≤ 1) :
    IsFiniteMeasure (weightedConditioned ν ℓ g) :=
  ⟨lt_of_le_of_lt (weightedConditioned_le ν ℓ g hg hgle Set.univ) (measure_lt_top _ _)⟩

lemma normalized_weightedConditioned_highSuffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) (hJ : 0 ≤ J)
    (g : Environment d → ℝ≥0∞)
    (hg : @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ g)
    (hgle : ∀ ω, g ω ≤ 1) (hpos : weightedConditioned ν ℓ g Set.univ ≠ 0) :
    (normalizedMeasure (weightedConditioned ν ℓ g)).map (highSuffix ℓ J) = conditionedLaw ν ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let : IsFiniteMeasure (weightedConditioned ν ℓ g) :=
    weightedConditioned_finite ν ℓ g (hg.mono (rowSigma_le _) le_rfl) hgle
  rw [normalizedMeasure,Measure.map_smul _ (measurable_highSuffix ℓ J hJ).aemeasurable,
    weightedConditioned_highSuffix ν ℓ htrans J hJ g hg hgle,
    smul_smul,ENNReal.inv_mul_cancel hpos (measure_ne_top _ _),one_smul]

lemma normalized_weightedConditioned_le {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) (hg : Measurable g) (hgle : ∀ ω, g ω ≤ 1)
    (c : ℝ≥0∞) (hc : c ≤ weightedConditioned ν ℓ g Set.univ) :
    normalizedMeasure (weightedConditioned ν ℓ g) ≤ c⁻¹ • conditionedLaw ν ℓ := by
  intro A
  change (weightedConditioned ν ℓ g Set.univ)⁻¹ * weightedConditioned ν ℓ g A ≤ c⁻¹ * conditionedLaw ν ℓ A
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hc) (weightedConditioned_le ν ℓ g hg hgle A)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
