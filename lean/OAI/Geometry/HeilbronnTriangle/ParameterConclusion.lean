import OAI.Geometry.HeilbronnTriangle.ParameterSequence
import OAI.Geometry.HeilbronnTriangle.SampleUpper
import OAI.Geometry.HeilbronnTriangle.FinalScalingBridge

namespace OAI


noncomputable section

namespace Problem355.Parameters

namespace PrimeParameterData

variable {k r : ℕ}

def sampleCard (P : PrimeParameterData k r) : ℕ :=
  ⌊(r : ℝ) * Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ))⌋₊

lemma sampleCard_le_power (P : PrimeParameterData k r) :
    (P.sampleCard : ℝ) ≤ Real.rpow (r : ℝ) (100000 * (k : ℝ)) := by
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast P.r_pos
  obtain ⟨hN, ht, _, _, hbox⟩ := P.real_bounds
  apply sample_size_le_real_power hr hN ht (by have := P.two_le_k; omega) hbox
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg r) (Real.sqrt_nonneg _))

end PrimeParameterData

theorem heilbronn_power_lower_bound_of_parameter_configurations
    {r : ℕ → ℕ} (D : (j : ℕ) → PrimeParameterData heilbronnK (r j))
    (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hconfig : ∀ᶠ j in Filter.atTop, ∃ P : Finset Point,
      P.card = (D j).sampleCard ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P ((D j).tau / (16 * ((D j).N : ℝ) ^ 3))) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  have hrR : Filter.Tendsto (fun j => (r j : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hr
  apply heilbronn_power_lower_bound_of_floor_configurations
    (fun j => (r j : ℝ)) (fun j => ((D j).N : ℝ))
    (fun j => ((D j).tau : ℝ)) hrR
  · exact Filter.Eventually.of_forall fun j =>
      ⟨Nat.cast_pos.mpr (D j).N_pos, Nat.cast_pos.mpr (D j).tau_pos,
        (D j).real_bounds.2.2.1⟩
  · exact Filter.Eventually.of_forall fun j => (D j).sampleCard_le_power
  · exact hconfig

theorem heilbronn_power_lower_bound_of_large_prime_configurations
    (hconstruction : ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → r.Prime → Odd r →
      ∀ D : PrimeParameterData heilbronnK r, ∃ P : Finset Point,
        P.card = D.sampleCard ∧ pointsInUnitSquare P ∧
        triangleAreasAtLeast P (D.tau / (16 * (D.N : ℝ) ^ 3))) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  obtain ⟨r0, hconstruction⟩ := hconstruction
  obtain ⟨r, D, hr, hprime⟩ := exists_heilbronn_parameter_sequence
  apply heilbronn_power_lower_bound_of_parameter_configurations D hr
  filter_upwards [hr.eventually_ge_atTop r0] with j hj
  exact hconstruction (r j) hj (hprime j).1 (hprime j).2.1 (D j)

end Problem355.Parameters

end

end OAI
