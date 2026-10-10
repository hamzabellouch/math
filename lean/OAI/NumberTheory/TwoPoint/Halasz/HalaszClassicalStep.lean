import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeSupply

namespace OAI

/-! The classical mean-value step using a finite supply of primes.
The absolute lower threshold for R comes only from Chebyshev's bounds. -/
namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem halasz_classical_step : ∃ R₀ : ℕ, ∀ s k N R : ℕ,
    0<s → 2≤k → (4*(k:ℝ)^2)^2<(N:ℝ) → k<R → N<R^k →
    R₀≤R → (2*(k^2*k)+1)^2≤R →
    halaszVinogradovCount (k+s) k N ≤
      2*(2*(k^2*k)+1)*((16*R)^(2*s)*((k^k*(16*R)^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/R+1)))) := by
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp halasz_prime_supply_card
  refine ⟨R₀,?_⟩
  intro s k N R hs hk hsize hkR hNR hR0 hmany
  have hroot : ((2*(k^2*k)+1:ℕ):ℝ)≤Real.sqrt (R:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hmany
  have hcard : 2*(k^2*k)+1≤(halaszPrimeSupply R).card := by
    exact_mod_cast hroot.trans (hR₀ R hR0)
  obtain ⟨P,hP,hPcard⟩ := exists_subset_card_eq hcard
  have hb : ∀ p∈P, p.Prime ∧ R≤p ∧ p≤16*R := by
    intro p hp
    have hh := halasz_prime_supply_mem (hP hp)
    exact ⟨hh.1,hh.2.1.le,hh.2.2⟩
  have h := halasz_vinogradov_prime_recurrence hs hk hsize hkR hNR P hb
    (by rw [hPcard]; omega)
  simpa only [hPcard] using h

end TwoPointCorrelations

end OAI
