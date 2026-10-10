import OAI.NumberTheory.Ostmann.ZeroDensity.GiantDensitySum

namespace OAI

/-! # Bounded densities on the common real giant rectangle -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def restrictedPrimeGiantDensity (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) : ℝ → ℂ :=
  (Set.Ioc u v).indicator (fun x => (selectedPrimeLogDensity P Q q a x : ℂ))

theorem measurable_restrictedPrimeGiantDensity (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) : Measurable (restrictedPrimeGiantDensity P Q q a u v) :=
  (Complex.continuous_ofReal.measurable.comp (measurable_selectedPrimeLogDensity P Q q a)).indicator
    measurableSet_Ioc

theorem restrictedPrimeGiantDensity_norm (P : PublishedProgressionInput) (Q q a : ℕ)
    (hq : 0 < q) (u v : ℝ) (hu : 1 ≤ u) (x : ℝ) :
    ‖restrictedPrimeGiantDensity P Q q a u v x‖ ≤ 2 := by
  by_cases hx : x ∈ Set.Ioc u v
  · simp only [restrictedPrimeGiantDensity, Set.indicator_of_mem hx,
      Complex.norm_real, Real.norm_eq_abs]
    exact primeLogDensity_abs_le_two _ _ _
      (by exact_mod_cast Nat.totient_pos.mpr hq) (pageCoefficient_abs_le_one _ _)
      (pageBeta_le_one _) (hu.trans hx.1.le)
  · simp only [restrictedPrimeGiantDensity, Set.indicator_of_notMem hx, norm_zero]
    norm_num

theorem primeGiantMeasure_restrict_integral (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 ≤ u) (f : ℝ → ℂ) :
    (∫ x, f x ∂primeGiantMeasure P Q q a u v) =
      ∫ x in Set.Ioc u v, f x * restrictedPrimeGiantDensity P Q q a u v x := by
  rw [primeGiantMeasure_integral P Q q a u v hu]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only [restrictedPrimeGiantDensity, Set.indicator_of_mem hx]

theorem primeGiantMeasure_pair_integral (P : PublishedProgressionInput) (Q q a b : ℕ)
    (u v r s : ℝ) (hu : 0 ≤ u) (hr : 0 ≤ r) (H : ℝ → ℝ → ℂ) :
    (∫ x, ∫ y, H x y ∂primeGiantMeasure P Q q b r s ∂primeGiantMeasure P Q q a u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        H x y * restrictedPrimeGiantDensity P Q q a u v x *
          restrictedPrimeGiantDensity P Q q b r s y := by
  rw [primeGiantMeasure_restrict_integral P Q q a u v hu]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  dsimp only
  rw [primeGiantMeasure_restrict_integral P Q q b r s hr, ← integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y _
  ring

theorem primeGiantMeasure_residue_integral (P : PublishedProgressionInput) (Q q : ℕ)
    (hq : 0 < q) (A B : Finset ℕ) (u v r s : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H)) (K : ℝ)
    (hK : ∀ x y, ‖H x y‖ ≤ K) (c : ℕ → ℕ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B,
      ∫ x, ∫ y, c a b * H x y ∂primeGiantMeasure P Q q b r s ∂primeGiantMeasure P Q q a u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s, H x y *
        (∑ a ∈ A, ∑ b ∈ B, c a b * restrictedPrimeGiantDensity P Q q a u v x *
          restrictedPrimeGiantDensity P Q q b r s y) := by
  simp_rw [primeGiantMeasure_pair_integral P Q q _ _ u v r s (by linarith) (by linarith)]
  exact bounded_density_pair_sum A B (volume.restrict (Set.Ioc u v)) (volume.restrict (Set.Ioc r s))
    H hH K hK (fun a => restrictedPrimeGiantDensity P Q q a u v)
    (fun b => restrictedPrimeGiantDensity P Q q b r s)
    (fun a _ => measurable_restrictedPrimeGiantDensity P Q q a u v)
    (fun b _ => measurable_restrictedPrimeGiantDensity P Q q b r s)
    2 2 (by norm_num) (by norm_num)
    (fun a _ x => restrictedPrimeGiantDensity_norm P Q q a hq u v hu x)
    (fun b _ x => restrictedPrimeGiantDensity_norm P Q q b hq r s hr x) c

noncomputable def restrictedIntegerGiantDensity (q : ℕ) (J u v : ℝ) : ℝ → ℂ :=
  (Set.Ioc u v).indicator (fun x => (integerLogDensity q J x : ℂ))

theorem measurable_restrictedIntegerGiantDensity (q : ℕ) (J u v : ℝ) :
    Measurable (restrictedIntegerGiantDensity q J u v) :=
  (Complex.continuous_ofReal.comp (continuous_integerLogDensity q J)).measurable.indicator
    measurableSet_Ioc

theorem restrictedIntegerGiantDensity_norm (q : ℕ) (hq : 0 < q) (J u v x : ℝ) :
    ‖restrictedIntegerGiantDensity q J u v x‖ ≤ Real.exp (v - J) := by
  by_cases hx : x ∈ Set.Ioc u v
  · simp only [restrictedIntegerGiantDensity, Set.indicator_of_mem hx,
      Complex.norm_real, Real.norm_eq_abs]
    exact integerLogDensity_abs_le q hq J hx.2
  · simp only [restrictedIntegerGiantDensity, Set.indicator_of_notMem hx, norm_zero]
    exact (Real.exp_pos _).le

theorem integerGiantMeasure_restrict_integral (q : ℕ) (J u v : ℝ) (f : ℝ → ℂ) :
    (∫ x, f x ∂integerGiantMeasure q J u v) =
      ∫ x in Set.Ioc u v, f x * restrictedIntegerGiantDensity q J u v x := by
  rw [integerGiantMeasure_integral q J u v]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only [restrictedIntegerGiantDensity, Set.indicator_of_mem hx]

theorem mixedGiantMeasure_pair_integral (P : PublishedProgressionInput) (Q q b : ℕ)
    (u v r s J : ℝ) (hr : 0 ≤ r) (H : ℝ → ℝ → ℂ) :
    (∫ x, ∫ y, H x y ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        H x y * restrictedIntegerGiantDensity q J u v x * restrictedPrimeGiantDensity P Q q b r s y := by
  rw [integerGiantMeasure_restrict_integral q J u v]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  dsimp only
  rw [primeGiantMeasure_restrict_integral P Q q b r s hr, ← integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y _
  ring

theorem mixedGiantMeasure_residue_integral (P : PublishedProgressionInput) (Q q : ℕ)
    (hq : 0 < q) (A B : Finset ℕ) (u v r s J : ℝ) (hr : 1 ≤ r)
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H)) (K : ℝ)
    (hK : ∀ x y, ‖H x y‖ ≤ K) (c : ℕ → ℕ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B,
      ∫ x, ∫ y, c a b * H x y ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s, H x y *
        (∑ a ∈ A, ∑ b ∈ B, c a b * restrictedIntegerGiantDensity q J u v x *
          restrictedPrimeGiantDensity P Q q b r s y) := by
  simp_rw [mixedGiantMeasure_pair_integral P Q q _ u v r s J (by linarith)]
  exact bounded_density_pair_sum A B (volume.restrict (Set.Ioc u v)) (volume.restrict (Set.Ioc r s))
    H hH K hK (fun _ => restrictedIntegerGiantDensity q J u v)
    (fun b => restrictedPrimeGiantDensity P Q q b r s)
    (fun _ _ => measurable_restrictedIntegerGiantDensity q J u v)
    (fun b _ => measurable_restrictedPrimeGiantDensity P Q q b r s)
    (Real.exp (v - J)) 2 (by positivity) (by norm_num)
    (fun _ _ x => restrictedIntegerGiantDensity_norm q hq J u v x)
    (fun b _ x => restrictedPrimeGiantDensity_norm P Q q b hq r s hr x) c

end Ostmann

end OAI
