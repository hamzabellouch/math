import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets

theorem source_jet_row_autCongr
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (e : K ≃ₐ[ℚ] L) (σ τ : K ≃ₐ[ℚ] K) (θ : K) (α : Fin 3 → ℕ) :
    e (θ ^ α 0 * σ θ ^ α 1 * (σ * τ) θ ^ α 2) =
      e θ ^ α 0 * (AlgEquiv.autCongr e σ) (e θ) ^ α 1 *
        (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) (e θ) ^ α 2 := by
  have he (φ : K ≃ₐ[ℚ] K) (x : K) : (AlgEquiv.autCongr e φ) (e x) = e (φ x) := by
    change e (φ (e.symm (e x))) = e (φ x)
    rw [e.symm_apply_apply]
  simp only [map_mul, map_pow, AlgEquiv.mul_apply, he]

end WeightedTorusJets


end SiegelZeros

end OAI
