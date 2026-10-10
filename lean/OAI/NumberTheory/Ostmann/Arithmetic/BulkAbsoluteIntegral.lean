import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.BulkHaarDensity
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSeparatedKernelBound

namespace OAI

/-! # Integrating the nonnegative arithmetic norm under the original Page density -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- The absolute residue average is integrated with the true harmonic box
volume. The Page factors remain inside the arithmetic norm estimate. -/
theorem bulk_absolute_integral_bound {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q M : ℕ) [NeZero M]
    (u v : J → ℝ) (hu : ∀ j, 0 < u j)
    (K : BulkIntegrand J) (a : (J → (ZMod M)ˣ) → ℂ) (W A : ℝ)
    (hW : 0 ≤ W) (hK : ∀ y, ‖K y‖ ≤ W)
    (hA : ∀ y : J → ℝ, (∀ j, y j ∈ Set.Ioc (u j) (v j)) →
      (Fintype.card (J → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ z, ‖a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A) :
    ‖∑ z : J → (ZMod M)ˣ, ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun j =>
      primeGiantMeasure P Q M (z j).val.val (u j) (v j))‖ ≤
      (W * A) * ∏ j, ∫ x in Set.Ioc (u j) (v j), (x : ℝ)⁻¹ := by
  let μ : J → Measure ℝ := fun j => volume.restrict (Set.Ioc (u j) (v j))
  have hi (j : J) : Integrable (fun x : ℝ => x⁻¹) (μ j) := by
    have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (u j) (v j)) :=
      continuousOn_inv₀.mono (fun x hx => ne_of_gt (lt_of_lt_of_le (hu j) hx.1))
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hp : Integrable (fun y : J → ℝ => ∏ j, (y j)⁻¹) (Measure.pi μ) :=
    Integrable.fintype_prod hi
  rw [bulk_page_residue_integral P Q (fun _ => M) (fun z j => (z j).val.val) u v hu (fun z => K.constMul (a z))]
  have hb : ∀ᵐ y ∂Measure.pi μ,
      ‖∑ z, (K.constMul (a z)) y *
        ∏ j, (selectedPrimeLogDensity P Q M (z j).val.val (y j) : ℂ)‖ ≤
      (W * A) * ∏ j, (y j)⁻¹ := by
    have hm : ∀ᵐ y ∂Measure.pi μ, ∀ j, y j ∈ Set.Ioc (u j) (v j) :=
      Filter.eventually_all.mpr (fun j =>
        (Measure.tendsto_eval_ae_ae (μ := μ) (i := j)).eventually (ae_restrict_mem measurableSet_Ioc))
    filter_upwards [hm] with y hy
    have hny (j : J) : 0 < y j := (hu j).trans (hy j).1
    have he : (∑ z, (K.constMul (a z)) y *
        ∏ j, (selectedPrimeLogDensity P Q M (z j).val.val (y j) : ℂ)) =
        K y * ∑ z, a z * ∏ j, (selectedPrimeLogDensity P Q M (z j).val.val (y j) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      change (a z * K y) * _ = _
      ring
    rw [he, bulk_prime_density_haar P Q M y a, norm_mul, norm_mul]
    have hmean : ‖(Fintype.card (J → (ZMod M)ˣ) : ℂ)⁻¹ *
        ∑ z, a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans (hA y hy)
    have hprod : ‖∏ j, (y j : ℂ)⁻¹‖ = ∏ j, (y j)⁻¹ := by
      rw [norm_prod]
      apply Finset.prod_congr rfl
      intro j _
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hny j).le]
    rw [hprod, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hK y) hmean (norm_nonneg _) hW)
      (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (hny j).le)
  have hn := norm_integral_le_of_norm_le (hp.const_mul (W * A)) hb
  simpa only [integral_const_mul, integral_fintype_prod_eq_prod] using hn

/-- Sum all original boxes with their unchanged reciprocal-prime normalizers. -/
theorem bulk_absolute_mixture_bound {J C : Type*} [Fintype J] [Fintype C]
    (P : PublishedProgressionInput) (Q M : ℕ) [NeZero M]
    (u v : J → C → ℝ) (hu : ∀ j c, 0 < u j c)
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (hmass : ∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2)
    (K : BulkIntegrand J) (a : (J → (ZMod M)ˣ) → ℂ) (W A : ℝ)
    (hW : 0 ≤ W) (hA0 : 0 ≤ A) (hK : ∀ y, ‖K y‖ ≤ W)
    (hA : ∀ y : J → ℝ, (∀ j, 0 ≤ y j) →
      (Fintype.card (J → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ z, ‖a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A) :
    ‖∑ z : J → (ZMod M)ˣ, ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun j =>
      bulkCellMixture (Z j) (fun c => primeGiantMeasure P Q M (z j).val.val (u j c) (v j c)))‖ ≤
      (W * A) * 2 ^ Fintype.card J := by
  let μ := fun (z : J → (ZMod M)ˣ) j c =>
    primeGiantMeasure P Q M (z j).val.val (u j c) (v j c)
  let _ : ∀ z j c, IsFiniteMeasure (μ z j c) := fun z j c =>
    finite_primeGiantMeasure P Q _ _ _ _ (hu j c)
  change ‖∑ z, ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun j => bulkCellMixture (Z j) (μ z j))‖ ≤ _
  rw [bulk_residue_mixture_integral Z hZ μ (fun z => K.constMul (a z))]
  let H := fun j c => ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹
  have hH (j : J) (c : C) : 0 ≤ H j c := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact inv_nonneg.mpr ((hu j c).trans hx.1).le
  apply bulk_box_sum_bound Z hZ H hH hmass (W * A) (mul_nonneg hW hA0)
  intro c
  exact bulk_absolute_integral_bound P Q M (fun j => u j (c j)) (fun j => v j (c j))
    (fun j => hu j (c j)) K a W A hW hK (fun y hy => hA y (fun j => ((hu j (c j)).trans (hy j).1).le))

end Ostmann

end OAI
