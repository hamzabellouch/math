import OAI.NumberTheory.Ostmann.ZeroDensity.BulkHaarDensity
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedAverageNorm

namespace OAI

/-! # Absolute bulk bounds retaining the frequency tests -/

namespace Ostmann
open scoped Classical BigOperators

/-- The absolute coefficient also separates exactly by CRT. In particular,
the frequency indicators are kept inside their original Haar average. -/
theorem bulk_absolute_density_crt {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (y : J → ℝ) (F : (J → (ZMod r)ˣ) → ℂ)
    (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ) :
    (∑ z, ‖F (bulkResidueEquiv r p hc z).1 * ∏ i, G i ((bulkResidueEquiv r p hc z).2 i)‖ *
      ∏ j, selectedPrimeLogDensity P Q (∏ i, bulkResidueModuli r p i) (z j).val.val (y j)) =
    (((Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ *
      ∑ a, ‖F a‖ * ∏ j, (pageGiantWeight P Q r (a j).val.val (y j)).re) *
      ∏ i, ((Fintype.card (J → (ZMod (p i))ˣ) : ℝ)⁻¹ * ∑ b, ‖G i b‖)) *
        ∏ j, (y j)⁻¹ := by
  have h := bulk_prime_density_crt r p hc P Q hpage y
    (fun a => (‖F a‖ : ℂ)) (fun i b => (‖G i b‖ : ℂ))
  simp only [norm_mul, norm_prod]
  simp only [pageGiantWeight, Complex.ofReal_re]
  simp only [pageGiantWeight] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

theorem bulk_absolute_density_le {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (y : J → ℝ) (hy : ∀ j, 0 ≤ y j)
    (F : (J → (ZMod r)ˣ) → ℂ) (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ)
    (B : I → ℝ)
    (hB : ∀ i, (Fintype.card (J → (ZMod (p i))ˣ) : ℝ)⁻¹ * ∑ b, ‖G i b‖ ≤ B i) :
    (∑ z, ‖F (bulkResidueEquiv r p hc z).1 * ∏ i, G i ((bulkResidueEquiv r p hc z).2 i)‖ *
      ∏ j, selectedPrimeLogDensity P Q (∏ i, bulkResidueModuli r p i) (z j).val.val (y j)) ≤
    ((2 ^ Fintype.card J * ((Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ * ∑ a, ‖F a‖)) *
      ∏ i, B i) * ∏ j, (y j)⁻¹ := by
  rw [bulk_absolute_density_crt r p hc P Q hpage y F G]
  have hlocal (i : I) : 0 ≤ (Fintype.card (J → (ZMod (p i))ˣ) : ℝ)⁻¹ * ∑ b, ‖G i b‖ :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun b _ => norm_nonneg _)
  have hmain :
      (Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ *
        ∑ a, ‖F a‖ * ∏ j, (pageGiantWeight P Q r (a j).val.val (y j)).re ≤
      2 ^ Fintype.card J * ((Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ * ∑ a, ‖F a‖) := by
    calc
      _ ≤ (Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ * ∑ a, ‖F a‖ * 2 ^ Fintype.card J := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc
          _ ≤ ∏ _j : J, (2 : ℝ) := Finset.prod_le_prod₀ (fun j _ =>
            (pageMultiplier_bounds _ _ _ (pageCoefficient_abs_le_one _) (pageBeta_le_one _)
              (hy j) _).1) (fun j _ =>
            (pageMultiplier_bounds _ _ _ (pageCoefficient_abs_le_one _) (pageBeta_le_one _)
              (hy j) _).2)
          _ = _ := by simp
      _ = _ := by rw [← Finset.sum_mul]; ring
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (hy j))
  apply mul_le_mul hmain (Finset.prod_le_prod₀ (fun i _ => hlocal i) (fun i _ => hB i))
    (Finset.prod_nonneg fun i _ => hlocal i)
  positivity

end Ostmann

end OAI
