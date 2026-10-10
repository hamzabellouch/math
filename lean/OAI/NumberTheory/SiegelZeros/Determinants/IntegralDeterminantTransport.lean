import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

open scoped NumberField
namespace WeightedTorusJets

theorem integral_determinant_transport
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (e : K ≃ₐ[ℚ] L) (Δ : 𝓞 K) :
    let Δ' := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv Δ
    (Δ' : L) = e (Δ : K) ∧
      (Δ' ≠ 0 ↔ Δ ≠ 0) ∧
      Algebra.norm ℚ (Δ' : L) = Algebra.norm ℚ (Δ : K) ∧
      Algebra.norm ℤ Δ' = Algebra.norm ℤ Δ ∧
      ∀ p n : ℕ,
        ((p : 𝓞 L) ^ n ∣ Δ' ↔ (p : 𝓞 K) ^ n ∣ Δ) ∧
        (Δ' ∈ (Ideal.span {(p : 𝓞 L)}) ^ n ↔
          Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ n) := by
  let eO := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  have hdiv (p n : ℕ) : (p : 𝓞 L) ^ n ∣ eO Δ ↔ (p : 𝓞 K) ^ n ∣ Δ := by
    simpa only [map_pow, map_natCast] using
      (map_dvd_iff eO (a := (p : 𝓞 K) ^ n) (b := Δ))
  refine ⟨rfl, eO.map_ne_zero_iff, ?_, ?_, ?_⟩
  · exact Algebra.norm_eq_of_algEquiv e (Δ : K)
  · exact Algebra.norm_eq_of_algEquiv eO.toIntAlgEquiv Δ
  · intro p n
    refine ⟨hdiv p n, ?_⟩
    simpa only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hdiv p n

end WeightedTorusJets


end SiegelZeros

end OAI
