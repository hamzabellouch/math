import OAI.Probability.SATComputability.IncidentMasks

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators NNReal

noncomputable def deletionMomentConstant : ℝ :=
  (48/5 : ℝ)*(∑' j, dyadicMomentCoefficient j) + (12/5 : ℝ)*(1200 : ℝ)^2

theorem deletionMomentConstant_nonneg : 0 ≤ deletionMomentConstant := by
  have hs : 0 ≤ ∑' j, dyadicMomentCoefficient j :=
    tsum_nonneg (fun j => dyadicMomentCoefficient_nonneg j)
  unfold deletionMomentConstant
  positivity

theorem capped_incident_error {n : ℕ} (hn : 0 < n) :
    ((60 : ℝ)/(n : ℝ))^2*((20*n : ℕ) : ℝ)^(6/5 : ℝ) ≤ (1200 : ℝ)^2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (1 : ℝ) ≤ ((20*n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 20*n by omega)
  have hp : ((20*n : ℕ) : ℝ)^(6/5 : ℝ) ≤ ((20*n : ℕ) : ℝ)^2 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hM
      (by norm_num : (6/5 : ℝ) ≤ (2 : ℕ))
  calc
    _ ≤ ((60 : ℝ)/(n : ℝ))^2*((20*n : ℕ) : ℝ)^2 :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = _ := by
      push_cast
      field_simp
      ring

theorem dominatingIncidentLaw_uniform_delay {n N : ℕ} [NeZero N]
    (hn : 0 < n) (r : ℝ≥0) (hr : (1 : ℝ)/8 ≤ r)
    (U : Finset (DeletionCandidate N)) :
    (dominatingIncidentLaw (n := N) (60 / (n : ℝ≥0))).expect
      (fun I => maskDelayMoment r 3 (20*n) U I) ≤ deletionMomentConstant := by
  apply (dominatingIncidentLaw_delay r hr (20*n) (60/(n : ℝ≥0)) U).trans
  unfold deletionMomentConstant
  apply add_le_add le_rfl
  simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (capped_incident_error hn) (by norm_num : (0 : ℝ) ≤ 12/5)

end FixedClauseThreshold.Computability

end OAI
