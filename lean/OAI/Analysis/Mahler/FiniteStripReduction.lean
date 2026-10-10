import OAI.Analysis.Mahler.StripVolume
import OAI.Analysis.Mahler.PlanarErrorRate
import Mathlib.Data.Nat.Factorial.Basic

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ENNReal
variable {n N : ℕ}

def StripMassBound (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) : Prop :=
  ENNReal.ofReal ((Real.pi*(m : ℝ))^n/(Nat.factorial n : ℝ)) ≤
    ∫⁻ z in stripSublevel A m, ENNReal.ofReal (stripHessianDet A m z)

/-- Finite-m normalization and polar-volume bound. Construction,
Jacobian, change-of-variables and image estimates follow from the hypotheses;
the only analytic premise is the mass lower bound. -/
theorem finite_strip_product_of_mass (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 2 ≤ m)
    (hmass : StripMassBound A m) :
    ENNReal.ofReal ((4 : ℝ)^n/(Nat.factorial n : ℝ)) ≤
      ENNReal.ofReal ((1+(N : ℝ)*planarError m)^n)*
        (volume (stripBody A)*volume (coordinatePolar (stripBody A))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpm : 0 < Real.pi*(m : ℝ) := mul_pos Real.pi_pos hm0
  have hc : 0 ≤ (4/(Real.pi*(m : ℝ)))^n := pow_nonneg (by positivity) _
  have he : (4/(Real.pi*(m : ℝ)))^n*((Real.pi*(m : ℝ))^n/(Nat.factorial n : ℝ)) =
      (4 : ℝ)^n/(Nat.factorial n : ℝ) := by
    rw [← mul_div_assoc,← mul_pow,div_mul_cancel₀ _ hpm.ne']
  have himage : ENNReal.ofReal ((4/(Real.pi*(m : ℝ)))^n)*
      (∫⁻ z in stripSublevel A m, ENNReal.ofReal (stripHessianDet A m z)) =
      volume (stripMap A m '' stripSublevel A m) := by
    rw [stripMap_volume_eq A hA hm]
    simp_rw [ENNReal.ofReal_mul hc]
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  calc
    _ = ENNReal.ofReal ((4/(Real.pi*(m : ℝ)))^n)*
        ENNReal.ofReal ((Real.pi*(m : ℝ))^n/(Nat.factorial n : ℝ)) := by
      rw [← ENNReal.ofReal_mul hc,he]
    _ ≤ ENNReal.ofReal ((4/(Real.pi*(m : ℝ)))^n)*
        (∫⁻ z in stripSublevel A m, ENNReal.ofReal (stripHessianDet A m z)) :=
      mul_le_mul_of_nonneg_left hmass zero_le
    _ = volume (stripMap A m '' stripSublevel A m) := himage
    _ ≤ volume (stripBody A)*(ENNReal.ofReal ((1+(N : ℝ)*planarError m)^n)*
        volume (coordinatePolar (stripBody A))) := stripMap_volume_le_product A hm
    _ = _ := by ac_rfl

/-- The finite-strip symmetric Mahler inequality follows from the exact
isolated-zero mass bound. No finiteness assumption on either volume is needed
for this extended-nonnegative-real formulation. -/
theorem finite_strip_mahler_of_mass (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A))
    (hmass : ∀ m : ℕ, 2 ≤ m → StripMassBound A m) :
    ENNReal.ofReal ((4 : ℝ)^n/(Nat.factorial n : ℝ)) ≤
      volume (stripBody A)*volume (coordinatePolar (stripBody A)) := by
  have hr : Tendsto (fun m : ℕ => (1+(N : ℝ)*planarError m)^n) atTop (𝓝 (1 : ℝ)) := by
    convert (tendsto_const_nhds.add (tendsto_const_nhds.mul planarError_nat_tendsto_zero)).pow n
      using 1 ; norm_num
  have he : Tendsto (fun m : ℕ => ENNReal.ofReal ((1+(N : ℝ)*planarError m)^n)) atTop (𝓝 1) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hr
  have hlim := ENNReal.Tendsto.mul he (Or.inl one_ne_zero)
    (tendsto_const_nhds (x := volume (stripBody A)*volume (coordinatePolar (stripBody A))))
    (Or.inr ENNReal.one_ne_top)
  simp only [one_mul] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨2,fun m hm =>
    finite_strip_product_of_mass A hA hm (hmass m hm)⟩)

end SymmetricMahler

end OAI
