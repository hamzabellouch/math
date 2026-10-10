import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexPrimeWeights

namespace OAI

/-! # Partition approximation without a partition-count loss -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexPrimeInterval_partition (q a : ℕ) (s : ℕ → ℝ) (hs : Monotone s)
    (w : ℝ → ℂ) (N : ℕ) :
    (∑ j ∈ Finset.range N, complexPrimeInterval q a (s j) (s (j + 1)) w) =
      complexPrimeInterval q a (s 0) (s N) w := by
  induction N with
  | zero => simp [complexPrimeInterval]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact complexPrimeInterval_add q a _ _ _ w (hs (Nat.zero_le _)) (hs (Nat.le_succ _))

theorem reciprocalPrimeInterval_partition (q a : ℕ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) :
    (∑ j ∈ Finset.range N, reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1)))) =
      reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) := by
  induction N with
  | zero => simp [reciprocalPrimeInterval]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact reciprocalPrimeInterval_add q a _ _ _
        (Real.exp_le_exp.mpr (hs (Nat.zero_le _))) (Real.exp_le_exp.mpr (hs (Nat.le_succ _)))

theorem integral_Ioc_partition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) (f : ℝ → E)
    (hf : ContinuousOn f (Set.Icc (s 0) (s N))) :
    (∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)), f y) =
      ∫ y in Set.Ioc (s 0) (s N), f y := by
  have heq (j : ℕ) : (∫ y in Set.Ioc (s j) (s (j + 1)), f y) =
      ∫ y in (s j)..(s (j + 1)), f y :=
    (intervalIntegral.integral_of_le (hs (Nat.le_succ _))).symm
  simp_rw [heq]
  rw [← intervalIntegral.integral_of_le (hs (Nat.zero_le _))]
  apply intervalIntegral.sum_integral_adjacent_intervals
  intro j hj
  apply (hf.mono ?_).intervalIntegrable_of_Icc (hs (Nat.le_succ _))
  intro y hy
  exact ⟨(hs (Nat.zero_le _)).trans hy.1, hy.2.trans (hs (by omega))⟩

/-- The oscillation error is proportional to total mass and total interval
length. The progression error is proportional to variation, with neither
error multiplied by the number of intervals. -/
theorem PublishedProgressionInput.prime_partition_variation (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (hs0 : 1 ≤ s 0) (N : ℕ) (hshort : s N ≤ s 0 + 1)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc (s 0) (s N))) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖w y - w (s j)‖ ≤ η) :
    ‖complexPrimeInterval q a (s 0) (s N) w -
        ∫ y in Set.Ioc (s 0) (s N), w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      discreteVariation (fun j => w (s j)) N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) +
      η * (reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) +
        2 * (s N - s 0)) := by
  let A (j : ℕ) := complexPrimeInterval q a (s j) (s (j + 1)) w
  let B (j : ℕ) := w (s j) * (reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) : ℂ)
  let C (j : ℕ) := w (s j) * (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y : ℝ)
  let D (j : ℕ) := ∫ y in Set.Ioc (s j) (s (j + 1)), w y * (selectedPrimeLogDensity P Q q a y : ℂ)
  have hρ : ContinuousOn (selectedPrimeLogDensity P Q q a) (Set.Icc (s 0) (s N)) :=
    continuousOn_primeLogDensity _ _ _ (by linarith)
  have hA : ‖∑ j ∈ Finset.range N, (A j - B j)‖ ≤
      η * reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, η * reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) := by
        apply Finset.sum_le_sum
        intro j hj
        exact complexPrimeInterval_freeze q a _ _ w _ η (hw j (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.mul_sum, reciprocalPrimeInterval_partition q a s hs N]
  have hD : ‖∑ j ∈ Finset.range N, (C j - D j)‖ ≤ 2 * η * (s N - s 0) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, 2 * η * (s (j + 1) - s j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_sub_rev]
        apply complex_density_integral_freeze _ _ _ _ _
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q))
          (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _)
          (hs0.trans (hs (Nat.zero_le _))) (hs (Nat.le_succ _)) w
        · apply hwc.mono
          intro y hy
          exact ⟨(hs (Nat.zero_le _)).trans hy.1,
            hy.2.trans (hs (by have := Finset.mem_range.mp hj; omega))⟩
        · exact hη
        · exact hw j (Finset.mem_range.mp hj)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub s]
  have hBC : ‖∑ j ∈ Finset.range N, (B j - C j)‖ ≤
      discreteVariation (fun j => w (s j)) N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) := by
    simpa only [B, C, ← mul_sub, ← Complex.ofReal_sub] using
      P.weighted_prime_interval_variation hQ hq hqQ ha s hs hs0 N hshort (fun j => w (s j))
  have hid : complexPrimeInterval q a (s 0) (s N) w -
        (∫ y in Set.Ioc (s 0) (s N), w y * (selectedPrimeLogDensity P Q q a y : ℂ)) =
      (∑ j ∈ Finset.range N, (A j - B j)) +
        (∑ j ∈ Finset.range N, (B j - C j)) + (∑ j ∈ Finset.range N, (C j - D j)) := by
    have hcont : ContinuousOn (fun y => w y * (selectedPrimeLogDensity P Q q a y : ℂ))
        (Set.Icc (s 0) (s N)) := hwc.mul (Complex.continuous_ofReal.comp_continuousOn hρ)
    rw [← complexPrimeInterval_partition q a s hs w N,
      ← integral_Ioc_partition s hs N (fun y => w y * (selectedPrimeLogDensity P Q q a y : ℂ)) hcont]
    simp only [Finset.sum_sub_distrib, A, D]
    ring
  rw [hid]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (by linarith [add_le_add (add_le_add hA hBC) hD])

end Ostmann

end OAI
