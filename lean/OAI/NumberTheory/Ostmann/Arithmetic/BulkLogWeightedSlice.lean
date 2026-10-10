import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogWeightedIntegrand

namespace OAI

/-! # One original bulk prime cell with all terminal logarithmic weights -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The full sharp paired kernel has the same derived one-coordinate Page
comparison, uniformly in every other real bulk coordinate. -/
theorem PublishedProgressionInput.bulk_log_weighted_kernel_slice_comparison
    (P : PublishedProgressionInput) {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (S : Finset σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (i : σ) (hiS : i ∈ S)
    (hT : ∀ b, (T b).CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r)
    (L R : ℝ) (f : BulkIntegrand σ)
    (hf : ∀ x, f x = realValueKernelPair (bulkLogValues base S x) childBound pivotBound T ψ X lo hi hlo hhi φ G L R)
    {t : ℕ} (slots : Fin t → List σ) (cb Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (rlog : ℕ) (hslots : ∀ j, (slots j).length ≤ rlog)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) (x : σ → ℝ) :
    letI := finite_primeGiantMeasure P Q q a u v (lt_of_lt_of_le zero_lt_one hu)
    ‖(f.withLogCutoffs base S cb slots).average (primeLogCellMeasure q a u v) i x -
        (f.withLogCutoffs base S cb slots).average (primeGiantMeasure P Q q a u v) i x‖ ≤
      bulkLogWeightedKernelPairBudget ψ V lo hi n d r 0 t rlog B D Dlog * bulkPrimeErrorFactor P Q u := by
  let _ := finite_primeGiantMeasure P Q q a u v (lt_of_lt_of_le zero_lt_one hu)
  let f' := f.withLogCutoffs base S cb slots
  let value := bulkLogValues base S x
  let H := fun y => ((∏ j, bulkLogCutoffWeight
    (Function.update value i (Real.exp y)) cb (slots j) : ℝ) : ℂ) * realValueKernelPair (Function.update value i (Real.exp y)) childBound pivotBound T
    ψ X lo hi hlo hhi φ G L R
  have hH (y : ℝ) : f' (Function.update x i y) = H y := by
    change ((∏ j, bulkLogCutoffWeight (bulkLogValues base S (Function.update x i y)) cb (slots j) : ℝ) : ℂ) *
      f (Function.update x i y) = H y
    rw [hf, bulkLogValues_update base S x i hiS]
  rw [f'.average_prime_eq_interval q a u v i x H hH,
    f'.average_page P Q q a u v (lt_of_lt_of_le zero_lt_one hu) i x]
  simp_rw [hH]
  have h := P.bulk_log_weighted_kernel_pair_prime_comparison value i childBound pivotBound T hT (Polynomial.C L) (Polynomial.C R)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r 0 hsize hregular
    (by simp) (by simp) slots cb Dlog hDlog hloglip rlog hslots hQ hq hqQ ha u v hu huv hshort
  simpa only [Polynomial.eval_C] using h

end Ostmann

end OAI
