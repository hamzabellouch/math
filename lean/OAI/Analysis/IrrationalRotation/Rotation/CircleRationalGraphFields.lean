import OAI.Analysis.IrrationalRotation.Rotation.CircleRationalGraphApproximants
import OAI.Analysis.IrrationalRotation.Operators.ProjectionFieldRepresentative

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.CircleParameterData

theorem rationalGraphIdentities_congr_ae (p : CircleParameterData) (θ : ℝ)
    {P Q : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ}
    (hPQ : P =ᵐ[circleMeasure] Q) :
    p.RationalGraphIdentities θ P ↔ p.RationalGraphIdentities θ Q := by
  have htrans : ∀ᵐ x ∂circleMeasure, ∀ (A : ℕ) (r : ℤ),
      P (x + p.rationalTranslation A r) = Q (x + p.rationalTranslation A r) := by
    apply ae_all_iff.mpr
    intro A
    apply ae_all_iff.mpr
    intro r
    have hmp : MeasurePreserving (fun x : Circle => x + p.rationalTranslation A r)
        circleMeasure circleMeasure := by
      change MeasurePreserving _ volume volume
      exact measurePreserving_add_right volume _
    exact hmp.quasiMeasurePreserving.ae (p := fun x => P x = Q x) hPQ
  constructor
  · intro h
    filter_upwards [h, hPQ, htrans] with x hx he hs
    intro A hA r
    rw [← he, ← hs A r]
    exact hx A hA r
  · intro h
    filter_upwards [h, hPQ, htrans] with x hx he hs
    intro A hA r
    rw [he, hs A r]
    exact hx A hA r

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem rationalGraphIdentities_of_ae_positive_orbits
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hP : ∀ᵐ x ∂circleMeasure, IsStarProjection (P x))
    (hPm : ∀ k : ℤ, Measurable (fun x => P x (lp.single 2 k 1)))
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂circleMeasure,
      (1 - P (CircleWeights.rotate θ (n : ℤ) x)).comp
        ((ratioDiagonal (p.floorCocycle θ)
          (x, CircleWeights.rotate θ (n : ℤ) x)).comp (P x)) = 0) :
    p.RationalGraphIdentities θ P := by
  obtain ⟨Q, hQ, hQm, hQP⟩ := Fields.exists_everywhere_projection_field
    circleMeasure P hP hPm
  apply (p.rationalGraphIdentities_congr_ae θ hQP).mp
  apply hp.rationalGraphIdentities_of_positive_orbits Q hQ hQm
  intro n hn
  have hmp : MeasurePreserving (CircleWeights.rotate θ (n : ℤ))
      circleMeasure circleMeasure := by
    change MeasurePreserving (fun x : Circle => x + (n : ℤ) • (θ : Circle)) volume volume
    exact measurePreserving_add_right volume _
  have hrot := hmp.quasiMeasurePreserving.ae (p := fun x => Q x = P x) hQP
  filter_upwards [hQP, hrot, horbit n hn] with x he hr hx
  rw [he, hr]
  exact hx

end Invariant233.CircleParameterLaws

end

end OAI
