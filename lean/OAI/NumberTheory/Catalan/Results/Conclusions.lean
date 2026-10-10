import OAI.NumberTheory.Catalan.Arithmetic.FinitePlaceAssembly
import OAI.NumberTheory.Catalan.Arithmetic.PrimeNonvanishing
import OAI.NumberTheory.Catalan.Determinants.RealDeterminantUpper

namespace OAI

section

namespace InternalCatalan

theorem catalan_irrational :
    Irrational (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
  change Irrational catalan
  rintro ⟨z, hz⟩
  have hfinite := (nonzeroPrimeScale_tendsto z).eventually
    (determinantRat_finite_place_threshold z)
  have hreal := (nonzeroPrimeScale_tendsto z).eventually
    eventually_realDeterminant_log_upper
  obtain ⟨k, hkfinite, hkreal⟩ := (hfinite.and hreal).exists
  have hf := hkfinite (determinantRat_nonzeroPrimeScale_ne_zero z k)
  have hr := hkreal (determinant_nonzeroPrimeScale_ne_zero hz k)
  rw [determinantRat_cast hz (nonzeroPrimeScale_prime z k).pos] at hf
  linarith [finitePlace_realPlace_threshold_gap]

end InternalCatalan

end

end OAI
