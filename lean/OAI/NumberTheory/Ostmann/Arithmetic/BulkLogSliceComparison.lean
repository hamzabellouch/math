import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogContinuity
import OAI.NumberTheory.Ostmann.Arithmetic.RealBulkPrimeComparison
import OAI.NumberTheory.Ostmann.Construction.PrimeLogCellMeasure

namespace OAI

/-! # Actual prime and Page averages of a bulk coordinate -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap BoundedContinuousFunction

noncomputable def bulkSmoothComparisonBudget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r : ℕ) (B D : ℝ) : ℝ :=
  (((2 ^ n + (2 ^ n - 1)) * (2 * (n * d) + r) + 1 : ℕ) : ℝ) *
    (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1))

noncomputable def bulkPrimeErrorFactor (P : PublishedProgressionInput) (Q : ℕ) (u : ℝ) : ℝ :=
  18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
    Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)

/-- An actual one-coordinate comparison, uniformly in the remaining real bulk
logarithms. The finite prime measure includes both boundary conventions exactly. -/
theorem PublishedProgressionInput.bulk_log_slice_comparison
    (P : PublishedProgressionInput) {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (S : Finset σ) {n : ℕ} (T : MovingSlotData σ n)
    (i : σ) (hiS : i ∈ S) (hT : T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r)
    (L R : ℝ) (f : (σ → ℝ) →ᵇ ℂ)
    (hf : ∀ x, f x = realValueSmoothWeight (bulkLogValues base S x) T ψ X lo hi hlo hhi φ G L R)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    let _ := finite_primeGiantMeasure P Q q a u v (by linarith : 0 < u)
    ‖coordinateAverage (primeLogCellMeasure q a u v) i f -
      coordinateAverage (primeGiantMeasure P Q q a u v) i f‖ ≤
        bulkSmoothComparisonBudget ψ V lo hi n d r B D * bulkPrimeErrorFactor P Q u := by
  let _ := finite_primeGiantMeasure P Q q a u v (by linarith : 0 < u)
  have hpoint (x : σ → ℝ) :
      ‖coordinateAverage (primeLogCellMeasure q a u v) i f x -
        coordinateAverage (primeGiantMeasure P Q q a u v) i f x‖ ≤
          bulkSmoothComparisonBudget ψ V lo hi n d r B D * bulkPrimeErrorFactor P Q u := by
    let value := bulkLogValues base S x
    have hprime : coordinateAverage (primeLogCellMeasure q a u v) i f x =
        realBulkPrimeSmoothSum value i T (Polynomial.C L) (Polynomial.C R)
          ψ X lo hi hlo hhi φ G q a u v := by
      rw [coordinateAverage_apply]
      change (∫ t, coordinateSlice f i x t ∂primeLogCellMeasure q a u v) = _
      rw [primeLogCellMeasure_integral]
      unfold realBulkPrimeSmoothSum
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (0 : ℝ) < p := by
        have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
        exact_mod_cast hpprime.pos
      change f (Function.update x i (Real.log p)) * _ = _
      rw [hf, bulkLogValues_update base S x i hiS, Real.exp_log hp0]
      simp only [Polynomial.eval_C, value]
    have hpage : coordinateAverage (primeGiantMeasure P Q q a u v) i f x =
        ∫ y in Set.Ioc u v,
          smoothPolynomialWeight (bulkSmoothFactors value i T (Polynomial.C L) (Polynomial.C R)
            ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) (Real.exp y) *
              (selectedPrimeLogDensity P Q q a y : ℂ) := by
      rw [coordinateAverage_apply, primeGiantMeasure_integral P Q q a u v (by linarith)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y _
      dsimp only
      rw [hf, bulkLogValues_update base S x i hiS,
        bulkSmoothFactors_value value i T hT _ _ ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout]
      simp only [Polynomial.eval_C, value]
    rw [hprime, hpage]
    have h := P.real_bulk_prime_comparison value i T hT (Polynomial.C L) (Polynomial.C R)
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r 0 hsize hregular
      (by simp) (by simp) hQ hq hqQ ha u v hu huv hshort
    simpa only [bulkSmoothComparisonBudget, bulkPrimeErrorFactor,
      MovingSlotData.bulkNodePolynomials_length, add_zero] using h
  have hnonneg := (norm_nonneg _).trans (hpoint (fun _ => 0))
  exact (BoundedContinuousFunction.norm_le hnonneg).mpr hpoint

end Ostmann

end OAI
