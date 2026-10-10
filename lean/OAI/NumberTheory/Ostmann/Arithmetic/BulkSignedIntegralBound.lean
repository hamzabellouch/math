import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkPageBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedAverageNorm

namespace OAI

/-! # Integrating the good-matching bulk gain with the retained Page factor -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem bulk_frequency_page_mean_le {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q r : ℕ) [NeZero r]
    (y : J → ℝ) (hy : ∀ j, 0 ≤ y j) (F : (J → (ZMod r)ˣ) → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀ a, ‖F a‖ ≤ C) :
    ‖bulkFrequencyPageMean P Q r y F‖ ≤ C * 2 ^ Fintype.card J := by
  have hc : (Fintype.card (J → (ZMod r)ˣ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold bulkFrequencyPageMean
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ * ∑ _a : J → (ZMod r)ˣ, C * 2 ^ Fintype.card J := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, norm_prod]
      apply mul_le_mul (hF a) _ (Finset.prod_nonneg fun j _ => norm_nonneg _) hC
      calc
        _ ≤ ∏ _j : J, (2 : ℝ) := Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
          (fun j _ => pageGiantWeight_norm_le_two P Q r (a j).val.val (y j) (hy j))
        _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem bulk_signed_integral_bound {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (u v : J → ℝ) (hu : ∀ j, 0 < u j)
    (F : (J → ℝ) → (J → (ZMod r)ˣ) → ℂ)
    (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hF : ∀ y, (∀ j, y j ∈ Set.Ioc (u j) (v j)) → ∀ a, ‖F y a‖ ≤ C)
    (hlocal : ∀ i, ‖(Fintype.card (J → (ZMod (p i))ˣ) : ℂ)⁻¹ * ∑ z, G i z‖ ≤ δ)
    (f : (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) → BulkIntegrand J)
    (hf : ∀ z y, f z y = F y (bulkResidueEquiv r p hc z).1 *
      ∏ i, G i ((bulkResidueEquiv r p hc z).2 i)) :
    ‖∑ z, ∫ y, f z y ∂Measure.pi (fun j =>
      primeGiantMeasure P Q (∏ i, bulkResidueModuli r p i) (z j).val.val (u j) (v j))‖ ≤
      (C * 2 ^ Fintype.card J) * δ ^ Fintype.card I *
        ∏ j, ∫ x in Set.Ioc (u j) (v j), (x : ℝ)⁻¹ := by
  let μ : J → Measure ℝ := fun j => volume.restrict (Set.Ioc (u j) (v j))
  have hi (j : J) : Integrable (fun x : ℝ => x⁻¹) (μ j) := by
    have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (u j) (v j)) :=
      continuousOn_inv₀.mono (fun x hx => ne_of_gt (lt_of_lt_of_le (hu j) hx.1))
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hp : Integrable (fun y : J → ℝ => ∏ j, (y j)⁻¹) (Measure.pi μ) :=
    Integrable.fintype_prod hi
  rw [bulk_page_residue_integral P Q (fun _ => ∏ i, bulkResidueModuli r p i)
    (fun z j => (z j).val.val) u v hu f]
  have hb : ∀ᵐ y ∂Measure.pi μ,
      ‖∑ z, f z y * ∏ j, (selectedPrimeLogDensity P Q (∏ i, bulkResidueModuli r p i)
        (z j).val.val (y j) : ℂ)‖ ≤
      ((C * 2 ^ Fintype.card J) * δ ^ Fintype.card I) * ∏ j, (y j)⁻¹ := by
    have hm : ∀ᵐ y ∂Measure.pi μ, ∀ j, y j ∈ Set.Ioc (u j) (v j) :=
      Filter.eventually_all.mpr (fun j =>
        (Measure.tendsto_eval_ae_ae (μ := μ) (i := j)).eventually (ae_restrict_mem measurableSet_Ioc))
    filter_upwards [hm] with y hy
    have hny (j : J) : 0 < y j := (hu j).trans (hy j).1
    simp_rw [hf]
    have hb := bulk_prime_density_norm r p hc P Q hpage y (F y) G δ hlocal
    have hw := bulk_frequency_page_mean_le P Q r y (fun j => (hny j).le) (F y) C hC (hF y hy)
    have he (j : J) : ‖(y j : ℂ)⁻¹‖ = (y j)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hny j).le]
    simp_rw [he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hw (pow_nonneg hδ _))
      (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (hny j).le))
  have hn := norm_integral_le_of_norm_le
    (hp.const_mul ((C * 2 ^ Fintype.card J) * δ ^ Fintype.card I)) hb
  simpa only [integral_const_mul, integral_fintype_prod_eq_prod] using hn

end Ostmann

end OAI
