import OAI.NumberTheory.Ostmann.Arithmetic.BulkKernelPairComparison
import OAI.NumberTheory.Ostmann.Arithmetic.BulkPrimeIntegrands

namespace OAI

/-! # The original paired kernel as a bounded measurable bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realValueKernelPair_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernelPair (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernelPair value T
        (fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernelPair, realValueKernel_nat value hv childBound pivotBound (T false) (hf false),
    realValueKernel_nat value hv childBound pivotBound (T true) (hf true)]
  rfl

noncomputable def bulkLogKernelPairIntegrand {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (S : Finset σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hT : ∀ b i, i ∈ S → (T b).CompensationAbsent i)
    (i : σ) (hiS : i ∈ S) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) : BulkIntegrand σ where
  toFun x := realValueKernelPair (bulkLogValues base S x) childBound pivotBound T ψ X lo hi hlo hhi φ G L R
  measurable := (measurable_bulkLogKernel base S childBound pivotBound (T false) (hT false)
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout L R).mul
    (Complex.continuous_conj.measurable.comp (measurable_bulkLogKernel base S childBound pivotBound
      (T true) (hT true) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout L R))
  bounded := by
    let W := movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)
    have hb (b : Bool) (x : σ → ℝ) := realValueKernel_norm (bulkLogValues base S x) i childBound pivotBound
      (T b) (hT b i hiS) ψ X lo hi V hlo hhi (hV b) φ G B D hB hD hφ hlip hout L R
    have hW : 0 ≤ W := (norm_nonneg _).trans (hb false base)
    refine ⟨W ^ 2, sq_nonneg _, fun x => ?_⟩
    rw [realValueKernelPair, norm_mul, Complex.norm_conj, pow_two]
    exact mul_le_mul (hb false x) (hb true x) (norm_nonneg _) hW

/-- The full sharp paired kernel has the same derived one-coordinate Page
comparison, uniformly in every other real bulk coordinate. -/
theorem PublishedProgressionInput.bulk_kernel_log_slice_comparison
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
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) (x : σ → ℝ) :
    letI := finite_primeGiantMeasure P Q q a u v (lt_of_lt_of_le zero_lt_one hu)
    ‖f.average (primeLogCellMeasure q a u v) i x - f.average (primeGiantMeasure P Q q a u v) i x‖ ≤
      bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q u := by
  let _ := finite_primeGiantMeasure P Q q a u v (lt_of_lt_of_le zero_lt_one hu)
  let value := bulkLogValues base S x
  let H := fun y => realValueKernelPair (Function.update value i (Real.exp y)) childBound pivotBound T
    ψ X lo hi hlo hhi φ G L R
  have hH (y : ℝ) : f (Function.update x i y) = H y := by
    rw [hf, bulkLogValues_update base S x i hiS]
  rw [f.average_prime_eq_interval q a u v i x H hH,
    f.average_page P Q q a u v (lt_of_lt_of_le zero_lt_one hu) i x]
  simp_rw [hH]
  have h := P.bulk_kernel_pair_prime_comparison value i childBound pivotBound T hT (Polynomial.C L) (Polynomial.C R)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r 0 hsize hregular
    (by simp) (by simp) hQ hq hqQ ha u v hu huv hshort
  simpa only [Polynomial.eval_C] using h

end Ostmann

end OAI
