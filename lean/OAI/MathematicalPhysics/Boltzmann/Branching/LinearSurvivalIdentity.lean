import OAI.MathematicalPhysics.Boltzmann.Branching.LinearCharacteristicBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakConservedMarginal

namespace OAI

/-! # The positive linear solution equals the survival-weighted source formula -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P]

omit [MeasurableSpace P] in
theorem linearSolution_eq_survival {T t : ℝ} (ht : t ∈ Icc 0 T)
    (a : ℝ) {k : ℝ × P → ℝ} (hk : ∀ z, 0 ≤ k z) (g : ℝ × P → ℝ) (p : P)
    (hki : IntervalIntegrable (fun s => k (s,p)) volume 0 T) :
    TransportPrimitive.linearSolution a (fun s => k (s,p)) (fun s => g (s,p)) t =
      timeSurvival (volume.restrict (Icc 0 T)) k (t,p)*a+
      survivalVolterra (volume.restrict (Icc 0 T))
        (twoTimeSurvival (volume.restrict (Icc 0 T)) k) g (t,p) := by
  have hsource := timePrimitive_eq_interval ht
    (fun z : ℝ × P => twoTimeSurvival (volume.restrict (Icc 0 T)) k ((t,p),z.1)*g z) p
  change survivalVolterra (volume.restrict (Icc 0 T))
    (twoTimeSurvival (volume.restrict (Icc 0 T)) k) g (t,p) = _ at hsource
  rw [TransportPrimitive.linearSolution_formula,hsource,timeSurvival,timePrimitive_eq_interval ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hs
  have h0s : IntervalIntegrable (fun r => k (r,p)) volume 0 s := by
    apply hki.mono_set
    rw [uIcc_of_le hs0.1,uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl (hs0.2.trans ht.2)
  have hst : IntervalIntegrable (fun r => k (r,p)) volume s t := by
    apply hki.mono_set
    rw [uIcc_of_le hs0.2,uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc hs0.1 ht.2
  have he := intervalIntegral.integral_add_adjacent_intervals h0s hst
  have hd : (∫ r in 0..t, k (r,p))-(∫ r in 0..s, k (r,p)) = ∫ r in s..t, k (r,p) := by
    linarith
  dsimp only
  rw [twoTimeSurvival_eq_interval ht hs0 hk p hki,hd]

end BoltzmannNonuniqueness.Published

end

end OAI
