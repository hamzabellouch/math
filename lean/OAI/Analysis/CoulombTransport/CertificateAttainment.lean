import OAI.Analysis.CoulombTransport.DualCertificate
import OAI.Analysis.CoulombTransport.OptimalLocalization
import OAI.Analysis.CoulombTransport.Calibration

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

open DualCertificate

namespace ShiftedCoulombCertificate

/-- A contact candidate calibrates the common marginal potential integral.
This constructs the abstract certificate without assuming the candidate is optimal. -/
def ofContactCandidate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, potentialSum v t ≤ coulombCost t + offset)
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    ShiftedCoulombCertificate mu (∫⁻ t, coulombCost t ∂pi0) where
  potential := potentialSum v
  shift := offset
  shift_ne_top := hoffset
  lower_bound := hbound
  integral_eq := by
    intro pi hpi
    have : IsProbabilityMeasure pi0 := hpi0.1
    rw [lintegral_potentialSum hpi hv, ← lintegral_potentialSum hpi0 hv,
      ← lintegral_add_offset pi0 coulombCost offset]
    exact lintegral_congr_ae hcontact

end ShiftedCoulombCertificate

/-- Finite marginal potential integral makes every contact candidate finite. -/
theorem candidateCost_lt_top_of_contact {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    (hvfinite : (∫⁻ x, v x ∂mu) ≠ ⊤) {offset : ℝ≥0∞}
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    (∫⁻ t, coulombCost t ∂pi0) < ⊤ := by
  have : IsProbabilityMeasure pi0 := hpi0.1
  have hsum : (∫⁻ t, coulombCost t ∂pi0) + offset ≠ ⊤ := by
    rw [← lintegral_add_offset pi0 coulombCost offset,
      ← lintegral_congr_ae hcontact, lintegral_potentialSum hpi0 hv]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hvfinite, hvfinite⟩, hvfinite⟩
  exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mp hsum).1

theorem attained_finite_of_contact_candidate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    (hvfinite : (∫⁻ x, v x ∂mu) ≠ ⊤) {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, potentialSum v t ≤ coulombCost t + offset)
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    KantorovichAttained mu ∧ kantorovichValue mu < ⊤ ∧
      kantorovichValue mu = (∫⁻ t, coulombCost t ∂pi0) ∧
      (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) =
        kantorovichValue mu + offset := by
  let cert := ShiftedCoulombCertificate.ofContactCandidate hpi0 hv hoffset hbound hcontact
  have hvalue := cert.value_eq hpi0 rfl
  refine ⟨cert.attained hpi0 rfl, ?_, hvalue, ?_⟩
  · rw [hvalue]
    exact candidateCost_lt_top_of_contact hpi0 hv hvfinite hcontact
  · rw [hvalue, ← lintegral_potentialSum hpi0 hv]
    exact cert.integral_eq pi0 hpi0

/-- The sum of the marginal potential over the three coordinates. -/
def triplePotential (p : E3 → ℝ≥0∞) (t : Triple) : ℝ≥0∞ :=
  p (tripleFst t) + p (tripleSnd t) + p (tripleThd t)

theorem measurable_triplePotential {p : E3 → ℝ≥0∞} (hp : Measurable p) :
    Measurable (triplePotential p) := DualCertificate.measurable_potentialSum hp

theorem IsThreeCoupling.ae_of_support_certificate {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {U : Set E3} (hU : MeasurableSet U)
    (hmu : ∀ᵐ x ∂mu, x ∈ U) {P : Triple → Prop}
    (hP : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U → P t) :
    ∀ᵐ t ∂pi, P t := by
  have hf : Measurable tripleFst := measurable_fst
  have hs : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have ht : Measurable tripleThd := measurable_snd.comp measurable_snd
  have h1 : ∀ᵐ t ∂pi, tripleFst t ∈ U :=
    (ae_map_iff hf.aemeasurable hU).mp (by rwa [hpi.2.1])
  have h2 : ∀ᵐ t ∂pi, tripleSnd t ∈ U :=
    (ae_map_iff hs.aemeasurable hU).mp (by rwa [hpi.2.2.1])
  have h3 : ∀ᵐ t ∂pi, tripleThd t ∈ U :=
    (ae_map_iff ht.aemeasurable hU).mp (by rwa [hpi.2.2.2])
  exact (h1.and (h2.and h3)).mono fun t h => hP t h.1 h.2.1 h.2.2

theorem certificate_optimality {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C) :
    (∫⁻ t, coulombCost t ∂pi0) = kantorovichValue mu ∧
      (∫⁻ t, coulombCost t ∂pi0) < ⊤ := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact ⟨h.2.2.1.symm, candidateCost_lt_top_of_contact hpi0 hp hpfinite hcontact⟩

theorem kantorovichAttained_of_certificate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C) :
    KantorovichAttained mu ∧ kantorovichValue mu < ⊤ := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact ⟨h.1, h.2.1⟩

theorem certificate_contact_of_optimal {mu : Measure E3} {pi0 pi : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) (hpi : IsThreeCoupling mu pi)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hcost : Measurable coulombCost)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu) :
    ∀ᵐ t ∂pi, triplePotential p t = coulombCost t + C := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact DualCertificate.ae_contact_of_optimal_coupling hpi hp hC h.2.1.ne
    hcost.aemeasurable (hbound pi hpi) h.2.2.2 hoptimal

end Problem356

end

end OAI
