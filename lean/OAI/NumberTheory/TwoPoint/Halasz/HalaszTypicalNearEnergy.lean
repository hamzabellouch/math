import OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseTranslation
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRestrictedEnergy

namespace OAI

/-! Near-frequency energy for the actual typical polynomial, with the
atypical density paid once in mean square. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem halasz_typical_near_energy {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) (A E U : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (hU : 0 < U)
    (hcenter : ∀ k ∈ Icc N (2 * N), ‖halaszPhaseMean F 0 k‖ ≤ A * k)
    (hnear : ∀ u ∈ Set.Icc (-U) U, ∀ k ∈ Icc N (2 * N),
      ‖halaszPhaseMean F u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean F 0 k‖ ≤ E * k) :
    (∫ u in -U..U, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N u‖ ^ 2) ≤
      16 * Real.exp 1 * (U / N + 2) *
        (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N +
      100 * Real.pi * A ^ 2 + 200 * U * E ^ 2 := by
  have hbase := halasz_near_dyadic_energy F hN A E U hA hE hU.le hcenter hnear
  have herr := halasz_exceptional_dyadic_energy J P F hF hN hU
  have ht : -U ≤ U := by linarith
  have hc1 : Continuous (mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N) :=
    mrtExponentialPolynomial_continuous _ _ _
  have hc2 : Continuous (mrtDyadicPolynomial F N) := mrtExponentialPolynomial_continuous _ _ _
  have hs := mrt_restricted_energy_split
    (mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N) (mrtDyadicPolynomial F N)
    hc1 hc2 hU.le (Set.Subset.refl (Set.Ioc (-U) U))
  rw [← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le ht] at hs
  simp_rw [norm_sub_rev] at hs
  calc
    _ ≤ 2 * (∫ u in -U..U, ‖mrtDyadicPolynomial F N u -
          mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N u‖ ^ 2) +
        2 * (∫ u in -U..U, ‖mrtDyadicPolynomial F N u‖ ^ 2) := hs
    _ ≤ 2 * (8 * Real.exp 1 * (U / N + 2) *
          (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N) +
        2 * (50 * Real.pi * A ^ 2 + 100 * U * E ^ 2) := by linarith
    _ = _ := by ring

end TwoPointCorrelations

end OAI
