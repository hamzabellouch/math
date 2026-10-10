import OAI.NumberTheory.Ostmann.Supply.NaturalResidueAverage
import OAI.NumberTheory.Ostmann.ZeroDensity.RestrictedGiantDensity

namespace OAI

/-! # The exact Haar residue factors inside the real giant integral -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def pageGiantWeight (P : PublishedProgressionInput) (Q q a : ℕ) (x : ℝ) : ℂ :=
  (pageMultiplier (fun a => pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero P Q))) x a : ℝ)

noncomputable def correctedPrimePairAverage (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (c : ℕ → ℕ → ℂ) (x y : ℝ) : ℂ :=
  (Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℂ)⁻¹ *
    ∑ z : (ZMod q)ˣ × (ZMod q)ˣ,
      c (z.1 : ZMod q).val (z.2 : ZMod q).val *
        pageGiantWeight P Q q (z.1 : ZMod q).val x * pageGiantWeight P Q q (z.2 : ZMod q).val y

noncomputable def correctedMixedPairAverage (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (c : ℕ → ℕ → ℂ) (y : ℝ) : ℂ :=
  (Fintype.card (ZMod q × (ZMod q)ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod q × (ZMod q)ˣ,
      c z.1.val (z.2 : ZMod q).val * pageGiantWeight P Q q (z.2 : ZMod q).val y

theorem selectedPrimeLogDensity_page (P : PublishedProgressionInput) (Q q a : ℕ) (x : ℝ) :
    (selectedPrimeLogDensity P Q q a x : ℂ) =
      pageGiantWeight P Q q a x / ((Nat.totient q : ℂ) * (x : ℂ)) := by
  simp only [selectedPrimeLogDensity, primeLogDensity, pageGiantWeight, pageMultiplier,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem prime_pair_density_haar (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (c : ℕ → ℕ → ℂ) (x y : ℝ) :
    (∑ a ∈ reducedResidues q, ∑ b ∈ reducedResidues q,
      c a b * (selectedPrimeLogDensity P Q q a x : ℂ) * (selectedPrimeLogDensity P Q q b y : ℂ)) =
      correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)) := by
  simp_rw [sum_reducedResidues_eq_units, selectedPrimeLogDensity_page]
  simp only [correctedPrimePairAverage, Fintype.card_prod, ZMod.card_units_eq_totient,
    Nat.cast_mul, Fintype.sum_prod_type, div_eq_mul_inv, mul_inv_rev, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem mixed_pair_density_haar (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (c : ℕ → ℕ → ℂ) (J x y : ℝ) :
    (∑ a ∈ Finset.range q, ∑ b ∈ reducedResidues q,
      c a b * (integerLogDensity q J x : ℂ) * (selectedPrimeLogDensity P Q q b y : ℂ)) =
      (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ) := by
  simp_rw [sum_range_eq_zmod, sum_reducedResidues_eq_units, selectedPrimeLogDensity_page]
  simp only [correctedMixedPairAverage, Fintype.card_prod, ZMod.card, ZMod.card_units_eq_totient,
    Nat.cast_mul, Fintype.sum_prod_type, integerLogDensity, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    div_eq_mul_inv, mul_inv_rev, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Ostmann

end OAI
