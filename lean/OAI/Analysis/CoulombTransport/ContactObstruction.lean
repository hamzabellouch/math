import OAI.Analysis.CoulombTransport.GraphBridge

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A contact condition for optimal couplings also holds along any optimal
admissible graph. This needs no measurable-set hypothesis on `Contact`. -/
lemma ae_contact_of_graphCost_eq {mu : Measure E3} [IsProbabilityMeasure mu]
    {Contact : Triple → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3)
    (hopt : graphCost mu T2 T3 = kantorovichValue mu) :
    ∀ᵐ x ∂mu, Contact (graphMap T2 T3 x) := by
  have hpi := graphMeasure_isThreeCoupling mu h2 h3
  have hcost : (∫⁻ t, coulombCost t ∂graphMeasure mu T2 T3) =
      kantorovichValue mu := (lintegral_graphMeasure mu h2.1 h3.1).trans hopt
  exact ae_of_ae_map (measurable_graphMap h2.1 h3.1).aemeasurable
    (hcontact (graphMeasure mu T2 T3) hpi hcost)

lemma noMongeOptimizer_of_contact_obstruction (mu : Measure E3) [IsProbabilityMeasure mu]
    {Contact : Triple → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    (hobstruction : ∀ T2 T3 : E3 → E3, Preserves mu T2 → Preserves mu T3 →
      ¬ (∀ᵐ x ∂mu, Contact (graphMap T2 T3 x))) :
    NoMongeOptimizer mu := by
  intro T2 T3 h2 h3
  refine lt_of_le_of_ne (kantorovichValue_le_graphCost mu h2 h3) ?_
  intro heq
  exact hobstruction T2 T3 h2 h3 (ae_contact_of_graphCost_eq hcontact h2 h3 heq.symm)

/-- Abstract branch-selection endgame. A contact triple whose first coordinate
lies in `B` forces its second coordinate to satisfy `Select`. If no preserving
map can satisfy that selection almost everywhere for an absolutely continuous
submeasure, no admissible graph is optimal. -/
lemma noMongeOptimizer_of_selection_obstruction
    (mu nu : Measure E3) [IsProbabilityMeasure mu]
    (hnu : nu ≪ mu) {B : Set E3} (hB : ∀ᵐ x ∂nu, x ∈ B)
    {Contact : Triple → Prop} {Select : E3 → E3 → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    (hselect : ∀ x y z : E3, x ∈ B → Contact (x, (y, z)) → Select x y)
    (hobstruction : ∀ T : E3 → E3, Preserves mu T →
      ¬ (∀ᵐ x ∂nu, Select x (T x))) :
    NoMongeOptimizer mu := by
  apply noMongeOptimizer_of_contact_obstruction mu hcontact
  intro T2 T3 h2 h3 hgraph
  apply hobstruction T2 h2
  have hgraph' : ∀ᵐ x ∂nu, Contact (graphMap T2 T3 x) := hnu.ae_le hgraph
  filter_upwards [hB, hgraph'] with x hx hcx
  exact hselect x (T2 x) (T3 x) hx hcx

end Problem356

end

end OAI
