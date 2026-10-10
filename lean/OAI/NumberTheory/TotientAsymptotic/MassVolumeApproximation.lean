import OAI.NumberTheory.TotientAsymptotic.OuterGrid

namespace OAI

/-! The actual arithmetic prime mass approximates the exact witness-union
volume, uniformly in all bounded nonnegative weights. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

theorem mass_banded_volume_approximation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      |M x H f/G x (m x)-bandedVolumeMass x H f/G x (m x)| ≤ δ H := by
  obtain ⟨Cp, hCp, hfinite⟩ := mass_banded_volume_error hbox
  obtain ⟨D, hD, houter⟩ := outer_grid_mass_bound hbox hmertens hren
  obtain ⟨ε, hε, hboundary⟩ := weighted_boundary_grid_error hbox hmertens hren hford
  let K := 4*(lam/rho)
  let δ := fun H => D*(Real.exp (K*cofactorScale H)*bandPrimeError Cp (9/10) H)+ε H
  refine ⟨δ, ?_, ?_⟩
  · simpa only [δ, mul_zero, add_zero] using
      ((cofactor_bandPrimeError_tendsto K hCp.le (by norm_num : (0 : ℝ)<9/10)).const_mul D).add hε
  · filter_upwards [houter, hboundary, eventually_ge_atTop 2] with H ho hb hH
    have hPH := P_lt_self hH
    filter_upwards [ho, hb, theta_eventually_mem,
      B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
      m_tendsto.eventually (eventually_ge_atTop H)] with x hox hbx hs hB hm
    intro f hf
    have he := hfinite hPH hm hs f hf
    have heq : (∑ d ∈ Finset.Icc 1 (tailValueBound H), (d : ℝ)⁻¹*
        ((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card*bandPrimeError Cp (9/10) H+
          ((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card-
            (gridInner (bandGrid x H) (bandedWitnessRegion x H d)).card))) =
        (∑ d ∈ Finset.Icc 1 (tailValueBound H), (d : ℝ)⁻¹*
          (gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card)*bandPrimeError Cp (9/10) H+
        (∑ d ∈ Finset.Icc 1 (tailValueBound H), (d : ℝ)⁻¹*
          (((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card : ℝ)-
            (gridInner (bandGrid x H) (bandedWitnessRegion x H d)).card)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    rw [heq] at he
    have he' := div_le_div_of_nonneg_right he (G_pos hB (m x)).le
    have ho' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hox (bandPrimeError_nonneg hCp.le (by norm_num : (0 : ℝ) < 9/10) H)) (G_pos hB (m x)).le
    have htop : (D*Real.exp (K*cofactorScale H)*G x (m x))*bandPrimeError Cp (9/10) H/G x (m x) =
        D*(Real.exp (K*cofactorScale H)*bandPrimeError Cp (9/10) H) := by
      field_simp [(G_pos hB (m x)).ne']
    change _ ≤ (D*Real.exp (K*cofactorScale H)*G x (m x))*bandPrimeError Cp (9/10) H/G x (m x) at ho'
    rw [htop] at ho'
    have htotal := add_le_add ho' hbx
    rw [← add_div] at htotal
    calc
      _ = |M x H f-bandedVolumeMass x H f|/G x (m x) := by
        rw [← sub_div, abs_div, abs_of_pos (G_pos hB _)]
      _ ≤ _ := he'
      _ ≤ δ H := htotal

/-- The complete mass-to-union-volume estimate, including removal of the
prime grid, all prefix perturbations, and all retained bands. -/
theorem mass_volume_coefficient_approximation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      |M x H f/G x (m x)-unionVolumeCoefficient H f x| ≤ δ H := by
  obtain ⟨δ, hδ, hm⟩ := mass_banded_volume_approximation hbox hmertens hren hford
  obtain ⟨ε, hε, hv⟩ := banded_volume_coefficient_approximation hbox hmertens hren hford
  refine ⟨fun H => δ H+ε H, by simpa using hδ.add hε, ?_⟩
  filter_upwards [hm, hv] with H hmH hvH
  filter_upwards [hmH, hvH] with x hmx hvx
  intro f hf
  exact (abs_sub_le (M x H f/G x (m x)) (bandedVolumeMass x H f/G x (m x))
    (unionVolumeCoefficient H f x)).trans (add_le_add (hmx f hf) (hvx f hf))

/-- The manuscript's finite arithmetic coefficient approximates each fixed
bounded nonnegative weight, with an error vanishing as the tail cut grows. -/
theorem mass_finite_coefficient_approximation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        |M x H f/G x (m x)-AH H f (theta x)| ≤ δ H+ε := by
  obtain ⟨δ, hδ, hm⟩ := mass_volume_coefficient_approximation hbox hmertens hren hford
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hm] with H hH
  intro f hf ε hε
  have ht := (unionVolumeCoefficient_limit hren H f).abs
  filter_upwards [hH, ht.eventually (eventually_lt_nhds (by simpa using hε : |(0 : ℝ)| < ε))] with x hx hlim
  exact (abs_sub_le (M x H f/G x (m x)) (unionVolumeCoefficient H f x)
    (AH H f (theta x))).trans (add_le_add (hx f hf) hlim.le)

end TotientAsymptotic

end

end OAI
