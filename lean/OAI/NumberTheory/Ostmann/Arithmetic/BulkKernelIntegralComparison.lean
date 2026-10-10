import OAI.NumberTheory.Ostmann.Arithmetic.BulkKernelJointComparison
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCoordinateInsertion

namespace OAI

/-! # The actual sharp kernel comparison on the selected bulk product -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem BulkIntegrand.integral_comparison {k : ℕ} (f : BulkIntegrand (Fin k))
    (μ ν : Fin k → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (hμ : ∀ i, (μ i).real Set.univ ≤ 2) (hν : ∀ i, (ν i).real Set.univ ≤ 2)
    (ε : Fin k → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (herr : ∀ i x, ‖f.average (μ i) i x - f.average (ν i) i x‖ ≤ ε i) :
    ‖(∫ x, f x ∂Measure.pi μ) - ∫ x, f x ∂Measure.pi ν‖ ≤
      2 ^ k * ∑ i, ε i := by
  have h := f.averages_comparison μ ν (List.finRange k) (List.nodup_finRange k)
    (fun i _ => hμ i) (fun i _ => hν i) ε (fun i _ => hε i)
    (fun i _ => herr i) (fun _ => 0)
  rw [f.averages_finRange, f.averages_finRange] at h
  simpa only [List.length_finRange, ← List.ofFn_eq_map, List.sum_ofFn] using h

/-- The published progression input compares the sharp paired kernel in the
actual selected coordinates, while every nonbulk coordinate remains fixed.
There is no assumption about a previously integrated slice. -/
theorem PublishedProgressionInput.bulk_kernel_integral_comparison
    (P : PublishedProgressionInput) {σ : Type*} [Fintype σ] {k n : ℕ}
    (base : σ → ℝ) (S : Finset σ) (e : Fin k ↪ σ) (he : ∀ i, e i ∈ S)
    (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
    (hT : ∀ b i, (T b).CompensationAbsent (e i))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r)
    (L R : ℝ) (f : BulkIntegrand σ)
    (hf : ∀ x, f x = realValueKernelPair (bulkLogValues base S x)
      childBound pivotBound T ψ X lo hi hlo hhi φ G L R)
    {Q : ℕ} (hQ : 2 ≤ Q) (q a : Fin k → ℕ) (u v : Fin k → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
    let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
    ‖(∫ y, f (bulkCoordinateInsert base e y) ∂Measure.pi μ) -
      ∫ y, f (bulkCoordinateInsert base e y) ∂Measure.pi ν‖ ≤
      2 ^ k * ∑ i, bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D *
        bulkPrimeErrorFactor P Q (u i) := by
  let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
  let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
  let _ : ∀ i, IsFiniteMeasure (ν i) := fun i =>
    finite_primeGiantMeasure P Q _ _ _ _ (lt_of_lt_of_le zero_lt_one (hu i))
  have hs (i : Fin k) (x : σ → ℝ) := P.bulk_kernel_log_slice_comparison
    base S childBound pivotBound T (e i) (he i) (fun b => hT b i)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f hf
    hQ (hq i) (hqQ i) (ha i) (u i) (v i) (hu i) (huv i) (hshort i) x
  have hμ (i) : (μ i).real Set.univ ≤ 2 := by
    rw [primeLogCellMeasure_mass]
    exact hmass i
  have hν (i) : (ν i).real Set.univ ≤ 2 :=
    primeGiantMeasure_mass_le_two P Q _ _ (hq i) _ _ (hu i) (huv i) (hshort i)
  apply (f.pullBulk base e).integral_comparison μ ν hμ hν _
    (fun i => (norm_nonneg _).trans (hs i base))
  intro i y
  have h := hs i (bulkCoordinateInsert base e y)
  change ‖((f.average (μ i) (e i)).pullBulk base e) y -
    ((f.average (ν i) (e i)).pullBulk base e) y‖ ≤ _ at h
  simpa only [BulkIntegrand.pullBulk_average] using h

end Ostmann

end OAI
