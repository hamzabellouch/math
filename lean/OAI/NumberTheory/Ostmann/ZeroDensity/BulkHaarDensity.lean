import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCRT

namespace OAI

/-! # The joint harmonic density exposes the exact bulk Haar average -/

namespace Ostmann
open scoped Classical BigOperators

/-- Every prime density contributes one Haar-unit normalization and one
harmonic factor. Page multipliers remain inside the residue average. -/
theorem bulk_prime_density_haar {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q M : ℕ) [NeZero M]
    (y : J → ℝ) (C : (J → (ZMod M)ˣ) → ℂ) :
    (∑ z, C z * ∏ j, (selectedPrimeLogDensity P Q M (z j).val.val (y j) : ℂ)) =
      ((Fintype.card (J → (ZMod M)ˣ) : ℂ)⁻¹ *
        ∑ z, C z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)) *
          ∏ j, (y j : ℂ)⁻¹ := by
  have hc : (Fintype.card (J → (ZMod M)ˣ) : ℂ) =
      (Nat.totient M : ℂ) ^ Fintype.card J := by
    simp only [Fintype.card_fun, ZMod.card_units_eq_totient, Nat.cast_pow]
  simp_rw [selectedPrimeLogDensity_page]
  simp only [hc, div_eq_mul_inv, mul_inv_rev, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ← inv_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The full density in the actual product modulus factors into the retained
frequency/Page average, independent spectator averages and harmonic densities. -/
theorem bulk_prime_density_crt {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (y : J → ℝ) (F : (J → (ZMod r)ˣ) → ℂ) (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ) :
    (∑ z, (F (bulkResidueEquiv r p hc z).1 * ∏ i, G i ((bulkResidueEquiv r p hc z).2 i)) *
      ∏ j, (selectedPrimeLogDensity P Q (∏ i, bulkResidueModuli r p i) (z j).val.val (y j) : ℂ)) =
      (((Fintype.card (J → (ZMod r)ˣ) : ℂ)⁻¹ *
        ∑ a, F a * ∏ j, pageGiantWeight P Q r (a j).val.val (y j)) *
        ∏ i, ((Fintype.card (J → (ZMod (p i))ˣ) : ℂ)⁻¹ * ∑ b, G i b)) *
        ∏ j, (y j : ℂ)⁻¹ := by
  rw [bulk_prime_density_haar]
  congr 1
  have h := bulk_residue_page_average r p hc P Q hpage y F G
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  ring

end Ostmann

end OAI
