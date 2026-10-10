import OAI.Probability.FreeIsing.Gaussian.LinearSignalTilt
import OAI.Probability.FreeIsing.Spins.PosteriorTilt

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem map_cond_spin_observation_eq_linearSignalTilt
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hpost : mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x))
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    Measure.map X (ProbabilityTheory.cond mu {x | S x = a}) =
      linearSignalTilt (Measure.map X mu) q (spinSign a) := by
  have hQ : Measurable (fun x => q (X x)) := hq.comp hX
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hQb : ∀ᵐ x ∂mu, |q (X x)| ≤ 1 := by
    have hb := ae_bdd_norm_condExp_of_ae_bdd_norm (m := mY.comap X) hSb
    filter_upwards [hb, hpost] with x hx hp
    simpa only [hp, Real.norm_eq_abs] using hx
  have hQi : Integrable (fun x => q (X x)) mu :=
    Integrable.of_bound hQ.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hQb)
  have ha : |spinSign a| ≤ 1 := by cases a <;> norm_num [spinSign]
  let : IsProbabilityMeasure (ProbabilityTheory.cond mu {x | S x = a}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rw [hfair]; norm_num)
  have hdi := (integrable_const (1 : ℝ)).add (hQi.const_mul (spinSign a))
  let : IsFiniteMeasure (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) :=
    isFiniteMeasure_withDensity_ofReal hdi.hasFiniteIntegral
  have hmap : Measure.map X (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) =
      linearSignalTilt (Measure.map X mu) q (spinSign a) := by
    unfold linearSignalTilt
    exact map_withDensity_comp (mu := mu) (f := X)
      (w := fun y => ENNReal.ofReal (1 + spinSign a * q y)) hX
      (ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul hq)))
  rw [← hmap]
  ext t ht
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  let f : Y → ℝ := t.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator ht
  have hfint : Integrable (fun x => f (X x)) mu := by
    refine Integrable.of_bound (hfm.comp hX).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : X x ∈ t <;> simp [f, hx])
  have hfsmall : StronglyMeasurable[mY.comap X] (fun x => f (X x)) :=
    (hfm.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  have hint : (∫ y, f y ∂Measure.map X (ProbabilityTheory.cond mu {x | S x = a})) =
      ∫ y, f y ∂Measure.map X (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) := by
    rw [integral_map hX.aemeasurable hfm.aestronglyMeasurable,
      integral_map hX.aemeasurable hfm.aestronglyMeasurable,
      integral_cond_spin_posterior_tilt hX.comap_le hS hfsmall hfint a hfair,
      integral_linearSignalTilt hQ hQb ha hfint,
      ← integral_const_mul,
      ← integral_add hfint ((integrable_boundedSignal_mul hQ hQb hfint).const_mul (spinSign a))]
    apply integral_congr_ae
    filter_upwards [hpost] with x hx
    rw [hx]
    ring
  simpa [f, integral_indicator ht, measureReal_def] using hint

end Problem367

end

end OAI
