import OAI.Analysis.CoulombTransport.Model

namespace OAI

universe uAlpha

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356
namespace DualCertificate

/-- The sum of a nonnegative supporting potential over the three coordinates.
A bounded signed potential can be shifted by a constant before using this sum. -/
def potentialSum (v : E3 → ℝ≥0∞) (t : Triple) : ℝ≥0∞ :=
  v (tripleFst t) + v (tripleSnd t) + v (tripleThd t)

lemma measurable_potentialSum {v : E3 → ℝ≥0∞} (hv : Measurable v) :
    Measurable (potentialSum v) := by
  exact ((hv.comp measurable_fst).add
    (hv.comp (measurable_fst.comp measurable_snd))).add
    (hv.comp (measurable_snd.comp measurable_snd))

/-- The integral of a coordinate potential sum depends only on the common marginal. -/
lemma lintegral_potentialSum {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {v : E3 → ℝ≥0∞} (hv : Measurable v) :
    (∫⁻ t, potentialSum v t ∂pi) =
      (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) := by
  have hf : Measurable tripleFst := measurable_fst
  have hs : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have ht : Measurable tripleThd := measurable_snd.comp measurable_snd
  simp only [potentialSum]
  have hfs : Measurable (fun t : Triple => v (tripleFst t) + v (tripleSnd t)) :=
    (hv.comp hf).add (hv.comp hs)
  have hf' : Measurable (fun t : Triple => v (tripleFst t)) := hv.comp hf
  rw [lintegral_add_left hfs,
    lintegral_add_left hf',
    ← lintegral_map hv hf, ← lintegral_map hv hs, ← lintegral_map hv ht,
    hpi.2.1, hpi.2.2.1, hpi.2.2.2]

/-- Adding a constant to a nonnegative cost shifts its integral by that constant
under a probability measure; no measurability assumption on the cost is needed. -/
lemma lintegral_add_offset {α : Type uAlpha} [MeasurableSpace α]
    (pi : Measure α) [IsProbabilityMeasure pi] (c : α → ℝ≥0∞) (offset : ℝ≥0∞) :
    (∫⁻ t, c t + offset ∂pi) = (∫⁻ t, c t ∂pi) + offset := by
  rw [lintegral_add_right c measurable_const]
  simp

/-- Complementary slackness for a shifted nonnegative certificate. -/
lemma ae_contact_of_equal_integrals {α : Type uAlpha} [MeasurableSpace α]
    {pi : Measure α} [IsProbabilityMeasure pi] {p c : α → ℝ≥0∞}
    {offset : ℝ≥0∞} (hc : AEMeasurable c pi)
    (hbound : p ≤ᵐ[pi] fun t => c t + offset)
    (hfinite : (∫⁻ t, p t ∂pi) ≠ ⊤)
    (heq : (∫⁻ t, p t ∂pi) = (∫⁻ t, c t ∂pi) + offset) :
    p =ᵐ[pi] fun t => c t + offset := by
  apply ae_eq_of_ae_le_of_lintegral_le hbound hfinite (hc.add aemeasurable_const)
  rw [lintegral_add_offset, heq]

/-- A finite shifted dual value forces every optimal coupling onto the
contact set.  The value identity is the sole input needed from dual optimality. -/
lemma ae_contact_of_optimal_coupling {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hfinite : kantorovichValue mu ≠ ⊤)
    (hcost : AEMeasurable coulombCost pi)
    (hbound : potentialSum v ≤ᵐ[pi] fun t => coulombCost t + offset)
    (hvalue : (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) =
      kantorovichValue mu + offset)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu) :
    potentialSum v =ᵐ[pi] fun t => coulombCost t + offset := by
  have : IsProbabilityMeasure pi := hpi.1
  have hid := lintegral_potentialSum hpi hv
  rw [hvalue] at hid
  exact ae_contact_of_equal_integrals hcost hbound
    (hid ▸ ENNReal.add_ne_top.mpr ⟨hfinite, hoffset⟩)
    (by rw [hoptimal]; exact hid)

/-- If a feasible coupling is not concentrated on contact, its cost is strictly
larger than a finite calibrated value. This is the contrapositive form needed
for the deterministic-selection obstruction. -/
lemma cost_strictly_above_of_noncontact {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    {offset value : ℝ≥0∞} (hoffset : offset ≠ ⊤) (hfinite : value ≠ ⊤)
    (hcost : AEMeasurable coulombCost pi)
    (hbound : potentialSum v ≤ᵐ[pi] fun t => coulombCost t + offset)
    (hvalue : (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) =
      value + offset)
    (hnoncontact : ¬ (potentialSum v =ᵐ[pi] fun t => coulombCost t + offset)) :
    value < ∫⁻ t, coulombCost t ∂pi := by
  have : IsProbabilityMeasure pi := hpi.1
  have hid := lintegral_potentialSum hpi hv
  rw [hvalue] at hid
  have hfreq : ∃ᵐ t ∂pi, potentialSum v t ≠ coulombCost t + offset := by
    change ¬ (∀ᵐ t ∂pi, potentialSum v t = coulombCost t + offset) at hnoncontact
    simpa only [Filter.Frequently, not_not] using hnoncontact
  have hstrict := lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
    (hcost.add aemeasurable_const)
    (hid ▸ ENNReal.add_ne_top.mpr ⟨hfinite, hoffset⟩) hbound hfreq
  change (∫⁻ t, potentialSum v t ∂pi) < (∫⁻ t, coulombCost t + offset ∂pi) at hstrict
  rw [hid, lintegral_add_offset] at hstrict
  exact (ENNReal.add_lt_add_iff_right hoffset).mp hstrict

end DualCertificate
end Problem356

end

end OAI
