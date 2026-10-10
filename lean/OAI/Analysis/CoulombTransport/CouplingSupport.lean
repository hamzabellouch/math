import OAI.Analysis.CoulombTransport.GraphBridge

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A property holding almost everywhere for the common marginal holds in all
three coordinates of every feasible coupling. No measurability of the property
is needed for this direction of transport. -/
lemma IsThreeCoupling.ae_coordinates {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {p : E3 → Prop} (hp : ∀ᵐ x ∂mu, p x) :
    ∀ᵐ t ∂pi, p (tripleFst t) ∧ p (tripleSnd t) ∧ p (tripleThd t) := by
  have h1 : ∀ᵐ t ∂pi, p (tripleFst t) := by
    apply ae_of_ae_map measurable_tripleFst.aemeasurable
    simpa only [hpi.2.1] using hp
  have h2 : ∀ᵐ t ∂pi, p (tripleSnd t) := by
    apply ae_of_ae_map measurable_tripleSnd.aemeasurable
    simpa only [hpi.2.2.1] using hp
  have h3 : ∀ᵐ t ∂pi, p (tripleThd t) := by
    apply ae_of_ae_map measurable_tripleThd.aemeasurable
    simpa only [hpi.2.2.2] using hp
  exact h1.and (h2.and h3)

/-- Full marginal mass on a measurable set gives almost-everywhere membership. -/
lemma ae_mem_of_probability_measure_eq_one {mu : Measure E3} [IsProbabilityMeasure mu]
    {U : Set E3} (hU : MeasurableSet U) (hfull : mu U = 1) :
    ∀ᵐ x ∂mu, x ∈ U := by
  rw [ae_iff]
  change mu Uᶜ = 0
  rw [measure_compl hU (by simp [hfull]), measure_univ, hfull, tsub_self]

/-- Every coupling of a probability carried by `U` is carried by `U³`. -/
lemma IsThreeCoupling.ae_mem_cube {mu : Measure E3} [IsProbabilityMeasure mu]
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    {U : Set E3} (hU : MeasurableSet U) (hfull : mu U = 1) :
    ∀ᵐ t ∂pi, tripleFst t ∈ U ∧ tripleSnd t ∈ U ∧ tripleThd t ∈ U :=
  hpi.ae_coordinates (ae_mem_of_probability_measure_eq_one hU hfull)

/-- A pointwise certificate on the full-mass cube may be used almost everywhere
against any feasible coupling. -/
lemma IsThreeCoupling.ae_of_on_cube {mu : Measure E3} [IsProbabilityMeasure mu]
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    {U : Set E3} (hU : MeasurableSet U) (hfull : mu U = 1)
    {P : Triple → Prop}
    (hP : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U → P t) :
    ∀ᵐ t ∂pi, P t := by
  filter_upwards [hpi.ae_mem_cube hU hfull] with t ht
  exact hP t ht.1 ht.2.1 ht.2.2

end Problem356

end

end OAI
