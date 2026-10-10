import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateVariationEquality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteSignOrder

namespace OAI

/-! # Constant weight signs along a generic profile line -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set

/-- The segment-volume bound and the finite support formula give constant
weight signs along an absolutely continuous profile line, as soon as the
generic finite label action supplies nonzero weights and a fixed count of
positive signs. -/
theorem profile_weight_signs_constant
    {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
    (D : PolycyclicRecognition.SupportDatum W I B)
    (h q : ℝ → W) (hc : Continuous h) {T c : ℝ} (hT : 0 ≤ T)
    (hq : ∀ i, IntervalIntegrable (fun t => D.weight i (q t)) volume 0 T)
    (hFTC : ∀ i t, t ∈ Icc 0 T →
      D.weight i (h t) = ∫ s in 0..t, D.weight i (q s))
    (hbound : ∀ b, ∀ᵐ t ∂volume.restrict (Icc 0 T), D.basisSupport b (q t) ≤ c)
    (hlower : T * c ≤ D.templateSupport (h '' Icc 0 T))
    (hnonzero : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 T), D.weight i (q t) ≠ 0)
    (n : ℕ) (hcard : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (Finset.univ.filter (fun i => 0 < D.weight i (q t))).card = n) :
    ∃ S : Finset I, ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      ∀ i, (0 < D.weight i (q t) ↔ i ∈ S) := by
  obtain ⟨τ, _, _, hleft, hright⟩ :=
    D.exists_ordered_weight_signs h q hc hT hq hFTC hbound hlower
  exact exists_constant_positive_signs (fun i t => D.weight i (q t)) τ n
    hnonzero hleft hright hcard

end PolycyclicRecognition.SupportDatum

end

end OAI
