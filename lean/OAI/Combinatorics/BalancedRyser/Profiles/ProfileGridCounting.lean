import Mathlib.MeasureTheory.Measure.Prod
import OAI.Combinatorics.BalancedRyser.Incidence.ProfileEmpiricalIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileGridProducts

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace Balanced.FiniteProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem empiricalProfileMeasure_real_apply (D C E : Finset (Line F))
    (s : Set Profile) (hs : MeasurableSet s) :
    (empiricalProfileMeasure D C E : Measure Profile).real s =
      (Fintype.card F : ℝ)⁻¹ *
        ∑ l ∈ E, if lineProfile D C l ∈ s then (1 : ℝ) else 0 := by
  rw [← integral_indicator_one hs, empiricalProfileMeasure_integral]
  simp only [Set.indicator_apply, Pi.one_apply]

theorem empiricalProfileMeasure_prod_real
    {Z : Type*} [MeasurableSpace Z] (D C E : Finset (Line F))
    (τ : Measure Z) [IsFiniteMeasure τ]
    (s : Set (Profile × Z)) (hs : MeasurableSet s) :
    ((empiricalProfileMeasure D C E : Measure Profile).prod τ).real s =
      (Fintype.card F : ℝ)⁻¹ *
        ∑ l ∈ E, τ.real {z | (lineProfile D C l, z) ∈ s} := by
  rw [measureReal_def, Measure.prod_apply hs, coe_empiricalProfileMeasure,
    lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹),
    ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  rfl

end Balanced.FiniteProfile

namespace Balanced.ProfileParameterGrids

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem rightGrid_empirical_prod_real (n : ℕ) (D C E : Finset (Line F))
    (s : Set (ℝ × Profile)) (hs : MeasurableSet s) :
    (((rightGrid n).toFiniteMeasure.prod (empiricalProfileMeasure D C E)) :
      Measure (ℝ × Profile)).real s =
      (∑ i ∈ Finset.range (n + 1), ∑ l ∈ E,
        if ((((i + 1 : ℕ) : ℝ) / (n + 1)), lineProfile D C l) ∈ s
          then (1 : ℝ) else 0) / ((n + 1) * (Fintype.card F : ℝ)) := by
  rw [rightGrid_prod_real n _ hs]
  have hsections : ∀ i : ℕ,
      (empiricalProfileMeasure D C E : Measure Profile).real
        {p | ((((i + 1 : ℕ) : ℝ) / (n + 1)), p) ∈ s} =
      (Fintype.card F : ℝ)⁻¹ * ∑ l ∈ E,
        if ((((i + 1 : ℕ) : ℝ) / (n + 1)), lineProfile D C l) ∈ s
          then (1 : ℝ) else 0 := by
    intro i
    exact FiniteProfile.empiricalProfileMeasure_real_apply D C E _
      (hs.preimage measurable_prodMk_left)
  simp_rw [hsections]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

theorem powerGrid_empirical_prod_real (γ : ℝ) (hγ : 0 ≤ γ)
    (n : ℕ) (D C E : Finset (Line F))
    (s : Set (ℝ × Profile)) (hs : MeasurableSet s) :
    (((powerGrid γ hγ n).toFiniteMeasure.prod (empiricalProfileMeasure D C E)) :
      Measure (ℝ × Profile)).real s =
      (∑ i ∈ Finset.range (n + 1), ∑ l ∈ E,
        if (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), lineProfile D C l) ∈ s
          then (1 : ℝ) else 0) / ((n + 1) * (Fintype.card F : ℝ)) := by
  rw [powerGrid_prod_real γ hγ n _ hs]
  have hsections : ∀ i : ℕ,
      (empiricalProfileMeasure D C E : Measure Profile).real
        {p | (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), p) ∈ s} =
      (Fintype.card F : ℝ)⁻¹ * ∑ l ∈ E,
        if (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), lineProfile D C l) ∈ s
          then (1 : ℝ) else 0 := by
    intro i
    exact FiniteProfile.empiricalProfileMeasure_real_apply D C E _
      (hs.preimage measurable_prodMk_left)
  simp_rw [hsections]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end Balanced.ProfileParameterGrids

namespace Balanced.ProfileParameterGrids

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem rightGrid_empirical_prod_real_expect (n : ℕ) (D C E : Finset (Line F))
    (hE : E.card = n + 1) (s : Set (ℝ × Profile)) (hs : MeasurableSet s) :
    (((rightGrid n).toFiniteMeasure.prod (empiricalProfileMeasure D C E)) :
      Measure (ℝ × Profile)).real s =
      (Fintype.card F : ℝ)⁻¹ * ∑ i : Fin (n + 1), 𝔼 l : E,
        if ((((i.val + 1 : ℕ) : ℝ) / (n + 1)), lineProfile D C l) ∈ s
          then (1 : ℝ) else 0 := by
  rw [rightGrid_empirical_prod_real n D C E s hs]
  simp_rw [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, hE]
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ l : E,
    if ((((i + 1 : ℕ) : ℝ) / (n + 1)), lineProfile D C l) ∈ s
      then (1 : ℝ) else 0)]
  have hsum (i : ℕ) := Finset.sum_coe_sort E (fun l =>
    if ((((i + 1 : ℕ) : ℝ) / (n + 1)), lineProfile D C l) ∈ s
      then (1 : ℝ) else 0)
  simp_rw [hsum]
  simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
  ac_rfl

theorem powerGrid_empirical_prod_real_expect (γ : ℝ) (hγ : 0 ≤ γ)
    (n : ℕ) (D C E : Finset (Line F)) (hE : E.card = n + 1)
    (s : Set (ℝ × Profile)) (hs : MeasurableSet s) :
    (((powerGrid γ hγ n).toFiniteMeasure.prod (empiricalProfileMeasure D C E)) :
      Measure (ℝ × Profile)).real s =
      (Fintype.card F : ℝ)⁻¹ * ∑ i : Fin (n + 1), 𝔼 l : E,
        if (((((i.val + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹),
          lineProfile D C l) ∈ s then (1 : ℝ) else 0 := by
  rw [powerGrid_empirical_prod_real γ hγ n D C E s hs]
  simp_rw [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, hE]
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ l : E,
    if (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), lineProfile D C l) ∈ s
      then (1 : ℝ) else 0)]
  have hsum (i : ℕ) := Finset.sum_coe_sort E (fun l =>
    if (((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹), lineProfile D C l) ∈ s
      then (1 : ℝ) else 0)
  simp_rw [hsum]
  simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
  ac_rfl

theorem rightGrid_empirical_prod_real_reindex (n : ℕ) (D C E : Finset (Line F))
    (e : E ≃ Fin (n + 1)) (s : Set (ℝ × Profile)) (hs : MeasurableSet s) :
    (((rightGrid n).toFiniteMeasure.prod (empiricalProfileMeasure D C E)) :
      Measure (ℝ × Profile)).real s =
      (Fintype.card F : ℝ)⁻¹ * ∑ i : E, 𝔼 l : E,
        if (((((e i).val + 1 : ℕ) : ℝ) / (n + 1)), lineProfile D C l) ∈ s
          then (1 : ℝ) else 0 := by
  have hE : E.card = n + 1 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr e
  rw [rightGrid_empirical_prod_real_expect n D C E hE s hs]
  congr 1
  exact (Equiv.sum_comp e _).symm

theorem powerGrid_empirical_prod_real_reindex (γ : ℝ) (hγ : 0 ≤ γ)
    (n : ℕ) (D C E : Finset (Line F)) (e : E ≃ Fin (n + 1))
    (s : Set (ℝ × Profile)) (hs : MeasurableSet s) :
    (((powerGrid γ hγ n).toFiniteMeasure.prod (empiricalProfileMeasure D C E)) :
      Measure (ℝ × Profile)).real s =
      (Fintype.card F : ℝ)⁻¹ * ∑ i : E, 𝔼 l : E,
        if ((((((e i).val + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹),
          lineProfile D C l) ∈ s then (1 : ℝ) else 0 := by
  have hE : E.card = n + 1 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr e
  rw [powerGrid_empirical_prod_real_expect γ hγ n D C E hE s hs]
  congr 1
  exact (Equiv.sum_comp e _).symm

end Balanced.ProfileParameterGrids

end

end OAI
