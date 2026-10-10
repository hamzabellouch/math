import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDefectEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFastTail

namespace OAI

/-! # The two-channel radial L² obstruction

A lower bound for the sum of the two squared amplitudes already excludes
joint square integrability. No fixed choice of a dominant channel is needed.
-/

open Set MeasureTheory Filter Topology

namespace DefocusingNLS

theorem radial_pair_energy_integrable (f g : ℝ → ℂ) (R : ℝ)
    (hf : IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R))
    (hg : IntegrableOn (fun r => r ^ (11 : ℕ) * ‖g r‖ ^ 2) (Ioi R)) :
    IntegrableOn (fun r => r ^ (11 : ℕ) * homogeneousPairEnergy (f r, g r)) (Ioi R) := by
  convert! hf.add hg using 1
  ext r
  simp only [homogeneousPairEnergy_eq_norms, Pi.add_apply]
  ring

theorem radial_pair_not_integrable_of_energy_lower
    (f g : ℝ → ℂ) (R beta c : ℝ) (hc : 0 < c) (hb : -6 ≤ beta)
    (hlower : ∀ᶠ r in atTop, c * r ^ (2 * beta) ≤ homogeneousPairEnergy (f r, g r)) :
    ¬ (IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R) ∧
      IntegrableOn (fun r => r ^ (11 : ℕ) * ‖g r‖ ^ 2) (Ioi R)) := by
  rintro ⟨hf, hg⟩
  have hE := radial_pair_energy_integrable f g R hf hg
  obtain ⟨T, hT⟩ := eventually_atTop.1 hlower
  let A := max (max R T) 1
  have hAR : R ≤ A := (le_max_left R T).trans (le_max_left _ _)
  have hAT : T ≤ A := (le_max_right R T).trans (le_max_left _ _)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  have hsmall : IntegrableOn (fun r : ℝ => c * r ^ (11 + 2 * beta)) (Ioi A) := by
    apply (hE.mono_set (Ioi_subset_Ioi hAR)).mono'
    · exact (measurable_const.mul (measurable_id.pow_const _)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hA.trans hr
    have hp : c * r ^ (11 + 2 * beta) = r ^ (11 : ℕ) * (c * r ^ (2 * beta)) := by
      rw [Real.rpow_add hr0]
      simp only [Real.rpow_ofNat]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hp]
    exact mul_le_mul_of_nonneg_left (hT r (hAT.trans hr.le)) (by positivity)
  have hpower : IntegrableOn (fun r : ℝ => r ^ (11 + 2 * beta)) (Ioi A) := by
    have h := hsmall.const_mul c⁻¹
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h
  exact (not_integrableOn_Ioi_rpow_of_neg_one_le (a := A) (by linarith)) hpower

theorem radial_pair_not_integrable_of_norm_lower
    (f g : ℝ → ℂ) (R beta c : ℝ) (hc : 0 < c) (hb : -6 ≤ beta)
    (hlower : ∀ᶠ r in atTop, c * r ^ beta ≤ ‖(f r, g r)‖) :
    ¬ (IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R) ∧
      IntegrableOn (fun r => r ^ (11 : ℕ) * ‖g r‖ ^ 2) (Ioi R)) := by
  apply radial_pair_not_integrable_of_energy_lower f g R beta (c ^ 2) (by positivity) hb
  filter_upwards [hlower, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ c * r ^ beta) (norm_nonneg _)).2 hr
  have hp : c ^ 2 * r ^ (2 * beta) = (c * r ^ beta) ^ 2 := by
    rw [mul_comm (2 : ℝ) beta, Real.rpow_mul hr0.le, Real.rpow_ofNat, mul_pow]
  rw [hp]
  exact hs.trans (homogeneousPairEnergy_lower _)

/-- Transfer a nonzero-defect energy lower bound through a derivative estimate. -/
theorem radial_pair_not_integrable_of_defect_bound
    (f g : ℝ → ℂ) (E : ℝ → ℝ) (R beta d c C : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hb : -6 ≤ beta - d)
    (hElower : ∀ᶠ r in atTop, c ≤ r ^ (2 * d) * E r)
    (hderiv : ∀ᶠ r in atTop, r ^ (2 * beta) * E r ≤ C * homogeneousPairEnergy (f r, g r)) :
    ¬ (IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R) ∧
      IntegrableOn (fun r => r ^ (11 : ℕ) * ‖g r‖ ^ 2) (Ioi R)) := by
  apply radial_pair_not_integrable_of_energy_lower f g R (beta - d) (c / C)
    (div_pos hc hC) hb
  filter_upwards [hElower, hderiv, eventually_gt_atTop (0 : ℝ)] with r hE hD hr
  have hp : r ^ (2 * (beta - d)) * r ^ (2 * d) = r ^ (2 * beta) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hr.le (2 * (beta - d)))
  rw [← mul_assoc, hp] at h
  apply (mul_le_mul_iff_right₀ hC).mp
  calc
    C * (c / C * r ^ (2 * (beta - d))) = c * r ^ (2 * (beta - d)) := by field_simp
    _ ≤ r ^ (2 * beta) * E r := by simpa only [mul_comm c] using h
    _ ≤ C * homogeneousPairEnergy (f r, g r) := hD

end DefocusingNLS

end OAI
