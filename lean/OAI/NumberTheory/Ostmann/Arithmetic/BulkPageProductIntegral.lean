import OAI.NumberTheory.Ostmann.ZeroDensity.BulkProductDensity

namespace OAI

/-! # The full Page density inside one product integral -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem bulk_page_product_integral {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q : ℕ) (q a : J → ℕ) (u v : J → ℝ)
    (hu : ∀ j, 0 < u j) (f : (J → ℝ) → ℂ) :
    (∫ x, f x ∂Measure.pi (fun j => primeGiantMeasure P Q (q j) (a j) (u j) (v j))) =
      ∫ x, f x * ∏ j, (selectedPrimeLogDensity P Q (q j) (a j) (x j) : ℂ)
        ∂Measure.pi (fun j => volume.restrict (Set.Ioc (u j) (v j))) := by
  let μ : J → Measure ℝ := fun j => volume.restrict (Set.Ioc (u j) (v j))
  let ρ : J → ℝ → ℝ := fun j x => max (selectedPrimeLogDensity P Q (q j) (a j) x) 0
  have hρ (j : J) : Measurable (ρ j) := (measurable_selectedPrimeLogDensity P Q (q j) (a j)).max measurable_const
  have hi (j : J) : Integrable (ρ j) (μ j) := by
    have hb : Integrable (selectedPrimeLogDensity P Q (q j) (a j)) (μ j) :=
      selectedPrimeLogDensity_integrable P Q (q j) (a j) (u j) (v j) (hu j)
    apply hb.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (max_eq_left (selectedPrimeLogDensity_nonneg P Q (q j) (a j)
      (u j) (v j) (hu j).le x hx)).symm
  have hpos (j : J) (x : ℝ) : 0 ≤ ρ j x := le_max_right _ _
  have he (j : J) : (μ j).withDensity (fun x => ENNReal.ofReal (ρ j x)) =
      primeGiantMeasure P Q (q j) (a j) (u j) (v j) := by
    unfold primeGiantMeasure intervalDensityMeasure
    congr 1
    funext x
    dsimp only [ρ]
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_eq_left bot_le
  have h := bulk_integral_product_density μ ρ hρ hi hpos f
  simp only [he] at h
  refine h.trans (integral_congr_ae ?_)
  have hm : ∀ᵐ x ∂Measure.pi μ, ∀ j, x j ∈ Set.Ioc (u j) (v j) :=
    Filter.eventually_all.mpr (fun j =>
      (Measure.tendsto_eval_ae_ae (μ := μ) (i := j)).eventually (ae_restrict_mem measurableSet_Ioc))
  filter_upwards [hm] with x hx
  congr 1
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  exact max_eq_left (selectedPrimeLogDensity_nonneg P Q (q j) (a j) (u j) (v j)
    (hu j).le (x j) (hx j))

end Ostmann

end OAI
