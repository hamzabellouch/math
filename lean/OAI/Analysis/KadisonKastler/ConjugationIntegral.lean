import OAI.Analysis.KadisonKastler.GaussianStateAverage

namespace OAI

/-! # Conjugating a vectorwise weighted operator integral -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryConj_weightedOperatorIntegral
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (u : unitary (H →L[ℂ] H)) (x : H) :
    unitaryConj u (weightedOperatorIntegral μ w hw F hm C hb) x =
      ∫ t, w t • unitaryConj u (F t) x ∂μ := by
  change (u : H →L[ℂ] H) (∫ t, w t • F t (star (u : H →L[ℂ] H) x) ∂μ) = _
  rw [← (u : H →L[ℂ] H).integral_comp_comm
    (integrable_weighted_operator_vector μ w hw F hm C hb _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => (u : H →L[ℂ] H).map_smul (w t) _

theorem unitaryConj_commute (u v : unitary (H →L[ℂ] H))
    (hc : Commute (u : H →L[ℂ] H) (v : H →L[ℂ] H)) (a : H →L[ℂ] H) :
    unitaryConj u (unitaryConj v a) = unitaryConj v (unitaryConj u a) := by
  rw [← unitaryConj_mul, ← unitaryConj_mul]
  have he : u * v = v * u := Subtype.ext hc.eq
  rw [he]

end

end KadisonKastler

end OAI
