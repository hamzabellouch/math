import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandNearEnergy

namespace OAI

/-! Transfer the proved centered energy to the actual frequency subsets
in the logarithmic prime-band partition. -/

namespace TwoPointCorrelations

open MeasureTheory Set

lemma halasz_restricted_near_energy (b : ℕ → ℂ) (N : ℕ)
    (t U A : ℝ) (hU : 0 ≤ U)
    (hnear : (∫ u in -U..U, ‖mrtDyadicPolynomial b N (t + u)‖^2) ≤ A)
    (E : Set ℝ) (hE : E ⊆ Ioc (t-U) (t+U)) :
    (∫ s in E, ‖mrtDyadicPolynomial b N s‖^2) ≤ A := by
  have hc : Continuous (fun s => ‖mrtDyadicPolynomial b N s‖^2) :=
    (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hab : t-U ≤ t+U := by linarith
  have he : (∫ u in -U..U, ‖mrtDyadicPolynomial b N (t + u)‖^2) =
      ∫ s in (t-U)..(t+U), ‖mrtDyadicPolynomial b N s‖^2 := by
    simpa only [sub_eq_add_neg, add_comm] using
      (intervalIntegral.integral_comp_add_left
        (fun s => ‖mrtDyadicPolynomial b N s‖^2) t (a := -U) (b := U))
  rw [he, intervalIntegral.integral_of_le hab] at hnear
  apply le_trans _ hnear
  exact setIntegral_mono_set
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (hc.intervalIntegrable _ _))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hE)

end TwoPointCorrelations

end OAI
