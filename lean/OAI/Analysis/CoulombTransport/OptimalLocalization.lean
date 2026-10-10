import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A nonnegative dual certificate after adding a finite constant to the cost.
The shift permits a signed bounded real-valued supporting potential. -/
structure ShiftedCoulombCertificate (mu : Measure E3) (value : ℝ≥0∞) where
  potential : Triple → ℝ≥0∞
  shift : ℝ≥0∞
  shift_ne_top : shift ≠ ⊤
  lower_bound : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
    ∀ᵐ t ∂pi, potential t ≤ coulombCost t + shift
  integral_eq : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
    (∫⁻ t, potential t ∂pi) = value + shift

namespace ShiftedCoulombCertificate

variable {mu : Measure E3} {value : ℝ≥0∞}

private theorem measurable_coulomb : Measurable coulombCost := by
  unfold coulombCost invDistance tripleFst tripleSnd tripleThd
  fun_prop

/-- A constant shift integrates to itself under any feasible coupling. -/
theorem lintegral_cost_add (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi) :
    (∫⁻ t, coulombCost t + cert.shift ∂pi) =
      (∫⁻ t, coulombCost t ∂pi) + cert.shift := by
  have : IsProbabilityMeasure pi := hpi.1
  rw [lintegral_add_right _ measurable_const]
  simp

/-- Every coupling has cost at least the certified value. -/
theorem le_cost (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi) :
    value ≤ ∫⁻ t, coulombCost t ∂pi := by
  apply (ENNReal.add_le_add_iff_right cert.shift_ne_top).mp
  rw [← cert.integral_eq pi hpi, ← cert.lintegral_cost_add hpi]
  exact lintegral_mono_ae (cert.lower_bound pi hpi)

/-- A feasible candidate matching a certificate realizes the exact infimum. -/
theorem value_eq (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hcost : (∫⁻ t, coulombCost t ∂pi) = value) :
    kantorovichValue mu = value := by
  apply le_antisymm
  · exact iInf_le_of_le pi (iInf_le_of_le hpi hcost.le)
  · exact le_iInf fun q => le_iInf fun hq => cert.le_cost hq

/-- A matching candidate supplies the attainment assertion. -/
theorem attained (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hcost : (∫⁻ t, coulombCost t ∂pi) = value) :
    KantorovichAttained mu := by
  exact ⟨pi, hpi, hcost.trans (cert.value_eq hpi hcost).symm⟩

/-- Equality of the finite primal and dual integrals forces equality almost
 everywhere in the supporting inequality. -/
theorem ae_contact (cert : ShiftedCoulombCertificate mu value)
    (hfinite : value ≠ ⊤) {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi)
    (hcost : (∫⁻ t, coulombCost t ∂pi) = value) :
    ∀ᵐ t ∂pi, cert.potential t = coulombCost t + cert.shift := by
  apply ae_eq_of_ae_le_of_lintegral_le (cert.lower_bound pi hpi)
  · rw [cert.integral_eq pi hpi]
    exact ENNReal.add_ne_top.mpr ⟨hfinite, cert.shift_ne_top⟩
  · exact (measurable_coulomb.add measurable_const).aemeasurable
  · rw [cert.lintegral_cost_add hpi, cert.integral_eq pi hpi, hcost]

/-- An optimal plan is concentrated on any prescribed set that contains the
contact locus of the supporting certificate. -/
theorem ae_mem_of_optimal (cert : ShiftedCoulombCertificate mu value)
    (hfinite : value ≠ ⊤) (hvalue : kantorovichValue mu = value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hopt : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {contact : Set Triple}
    (hcontact : ∀ t, cert.potential t = coulombCost t + cert.shift → t ∈ contact) :
    ∀ᵐ t ∂pi, t ∈ contact := by
  exact (cert.ae_contact hfinite hpi (hopt.trans hvalue)).mono hcontact

end ShiftedCoulombCertificate

theorem noMongeOptimizer_of_ne
    {mu : Measure E3}
    (hlower : ∀ T2 T3, Preserves mu T2 → Preserves mu T3 →
      kantorovichValue mu ≤ graphCost mu T2 T3)
    (hne : ∀ T2 T3, Preserves mu T2 → Preserves mu T3 →
      graphCost mu T2 T3 ≠ kantorovichValue mu) :
    NoMongeOptimizer mu := by
  intro T2 T3 h2 h3
  exact lt_of_le_of_ne (hlower T2 T3 h2 h3) (hne T2 T3 h2 h3).symm

end Problem356

end

end OAI
