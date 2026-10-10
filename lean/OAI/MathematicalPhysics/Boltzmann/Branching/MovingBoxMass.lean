import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap

namespace OAI

/-! # The moving-box mass cap in characteristic coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

def flightMeasurableEquiv (t : ℝ) : (Velocity × Velocity) ≃ᵐ (Velocity × Velocity) where
  toFun := flight t
  invFun := flight (-t)
  left_inv p := by
    apply Prod.ext
    · dsimp [flight]; module
    · rfl
  right_inv p := by
    apply Prod.ext
    · dsimp [flight]; module
    · rfl
  measurable_toFun := by
    change Measurable (flight t)
    exact (flight_measurePreserving t).measurable
  measurable_invFun := by
    change Measurable (flight (-t))
    exact (flight_measurePreserving (-t)).measurable

theorem density_movingBox_bound {q κ d t : ℝ} (hq : q < 2) (hκ : 0 ≤ κ)
    (hd : 0 ≤ d) (ht : 0 ≤ t) {F : Velocity × Velocity → ℝ} (hF : Measurable F)
    (hbound : ∀ᵐ p ∂volume, F p ≤ (t+1)*H q p.2) :
    positiveDensityMeasure volume F ((flight t) ⁻¹' ReferenceGeometry.lateBox κ d t) ≤
      ENNReal.ofReal (ReferenceGeometry.lateBoxCapConstant q κ d*(1+t)^4) := by
  have hback : ∀ᵐ p ∂volume, F (flight (-t) p) ≤ (t+1)*H q p.2 :=
    (flight_measurePreserving (-t)).quasiMeasurePreserving.ae hbound
  have hmap : (positiveDensityMeasure volume F).map (flight t) =
      positiveDensityMeasure volume (fun p => F (flight (-t) p)) := by
    have h := positiveDensityMeasure_map_symm (flightMeasurableEquiv (-t))
      (flight_measurePreserving (-t)) hF
    change (positiveDensityMeasure volume F).map (flight (-(-t))) =
      positiveDensityMeasure volume (fun p => F (flight (-t) p)) at h
    simpa only [neg_neg] using h
  rw [← Measure.map_apply (flight_measurePreserving t).measurable
    (ReferenceGeometry.lateBox_measurable κ d t),hmap]
  exact ReferenceGeometry.density_lateBox_bound hq hκ hd ht hback

end BoltzmannNonuniqueness.EuclideanFlight

end

end OAI
