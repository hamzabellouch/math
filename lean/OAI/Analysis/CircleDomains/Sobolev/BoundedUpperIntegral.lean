import OAI.Analysis.CircleDomains.Modulus.HitNormTopology
import Mathlib.MeasureTheory.Constructions.UnitInterval

namespace OAI

/-! Weak upper semicontinuity of integrals of bounded upper semicontinuous tests.
For a test between zero and one, its integral is the product measure of its
closed hypograph in the product with the unit interval. Thus the closed-set Portmanteau theorem suffices. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal unitInterval

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

def unitIntervalProbability : ProbabilityMeasure I := ⟨volume, inferInstance⟩

omit [SecondCountableTopology X] in
private theorem hypograph_probability_eq_lintegral
    {f : X → ℝ} (hf : UpperSemicontinuous f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (μ : ProbabilityMeasure X) :
    ((μ.prod unitIntervalProbability : ProbabilityMeasure (X × I)) : Measure (X × I))
      {p | (p.2 : ℝ) ≤ f p.1} = ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) := by
  have hH : IsClosed {p : X × I | (p.2 : ℝ) ≤ f p.1} :=
    hf.IsClosed_hypograph.preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  change (μ : Measure X).prod (volume : Measure I) _ = _
  rw [Measure.prod_apply hH.measurableSet]
  apply lintegral_congr
  intro x
  have he : (Prod.mk x ⁻¹' {p : X × I | (p.2 : ℝ) ≤ f p.1}) =
      Iic (⟨f x, hf0 x, hf1 x⟩ : I) := rfl
  rw [he, unitInterval.volume_Iic]

theorem upperSemicontinuous_integral_unit_bounded
    {f : X → ℝ} (hf : UpperSemicontinuous f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    UpperSemicontinuous (fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X)) := by
  let H : Set (X × I) := {p | (p.2 : ℝ) ≤ f p.1}
  have hH : IsClosed H := hf.IsClosed_hypograph.preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hprod : Continuous (fun μ : ProbabilityMeasure X => μ.prod unitIntervalProbability) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_const)
  have hupper : UpperSemicontinuous (fun μ : ProbabilityMeasure X =>
      ((μ.prod unitIntervalProbability : ProbabilityMeasure (X × I)) : Measure (X × I)) H) := by
    apply upperSemicontinuous_iff_limsup_le.mpr
    intro μ
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hprod.continuousAt hH
  have heq (μ : ProbabilityMeasure X) :
      ∫ x, f x ∂(μ : Measure X) =
        (((μ.prod unitIntervalProbability : ProbabilityMeasure (X × I)) : Measure (X × I)) H).toReal := by
    rw [hypograph_probability_eq_lintegral hf hf0 hf1]
    have he := integral_toReal (hf.measurable.ennreal_ofReal.aemeasurable (μ := (μ : Measure X)))
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
    simpa only [ENNReal.toReal_ofReal (hf0 _)] using he
  intro μ c hc
  change (∫ x, f x ∂(μ : Measure X)) < c at hc
  change ∀ᶠ ν : ProbabilityMeasure X in 𝓝 μ, (∫ x, f x ∂(ν : Measure X)) < c
  rw [heq] at hc
  have hfin : ((μ.prod unitIntervalProbability : Measure (X × I)) H) ≠ ∞ := measure_ne_top _ _
  filter_upwards [hupper μ (ENNReal.ofReal c)
    ((ENNReal.lt_ofReal_iff_toReal_lt hfin).mpr hc)] with ν hν
  rw [heq]
  exact ENNReal.toReal_lt_of_lt_ofReal hν

theorem upperSemicontinuous_integral_bounded
    {f : X → ℝ} (hf : UpperSemicontinuous f) (hf0 : ∀ x, 0 ≤ f x)
    {M : ℝ} (hM : 0 < M) (hfM : ∀ x, f x ≤ M) :
    UpperSemicontinuous (fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X)) := by
  let g : X → ℝ := fun x => f x / M
  have hg : UpperSemicontinuous g :=
    (continuous_id.div_const M).comp_upperSemicontinuous hf
      (fun _ _ h => div_le_div_of_nonneg_right h hM.le)
  have hg0 (x : X) : 0 ≤ g x := div_nonneg (hf0 x) hM.le
  have hg1 (x : X) : g x ≤ 1 := (div_le_one hM).mpr (hfM x)
  have hu := upperSemicontinuous_integral_unit_bounded hg hg0 hg1
  have heq : (fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X)) =
      fun μ : ProbabilityMeasure X => M * ∫ x, g x ∂(μ : Measure X) := by
    funext μ
    rw [← integral_const_mul]
    congr 1
    funext x
    dsimp only [g]
    field_simp
  rw [heq]
  exact (continuous_const.mul continuous_id).comp_upperSemicontinuous hu
    (fun _ _ h => mul_le_mul_of_nonneg_left h hM.le)

end CircleDomainRigidity

end

end OAI
