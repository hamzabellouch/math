import OAI.NumberTheory.Ostmann.Arithmetic.IndexedBulkKernelComparison
import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogWeightedSlice

namespace OAI

/-! # Retained logarithmic weights in the original bulk-coordinate integral -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.bulk_log_weighted_integral_comparison_indexed
    (P : PublishedProgressionInput) {σ J : Type*} [Fintype σ] [Fintype J] {n : ℕ}
    (base : σ → ℝ) (S : Finset σ) (e : J ↪ σ) (he : ∀ i, e i ∈ S)
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
    {t : ℕ} (slots : Fin t → List σ) (cb Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (rlog : ℕ) (hslots : ∀ j, (slots j).length ≤ rlog)
    {Q : ℕ} (hQ : 2 ≤ Q) (q a : J → ℕ) (u v : J → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
    let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
    ‖(∫ y, (f.withLogCutoffs base S cb slots) (bulkCoordinateInsert base e y) ∂Measure.pi μ) -
      ∫ y, (f.withLogCutoffs base S cb slots) (bulkCoordinateInsert base e y) ∂Measure.pi ν‖ ≤
      2 ^ Fintype.card J * ∑ i, bulkLogWeightedKernelPairBudget ψ V lo hi n d r 0 t rlog B D Dlog *
        bulkPrimeErrorFactor P Q (u i) := by
  let f' := f.withLogCutoffs base S cb slots
  let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
  let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
  let _ : ∀ i, IsFiniteMeasure (ν i) := fun i =>
    finite_primeGiantMeasure P Q _ _ _ _ (lt_of_lt_of_le zero_lt_one (hu i))
  have hs (i : J) (x : σ → ℝ) := P.bulk_log_weighted_kernel_slice_comparison
    base S childBound pivotBound T (e i) (he i) (fun b => hT b i)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f hf
    slots cb Dlog hDlog hloglip rlog hslots hQ (hq i) (hqQ i) (ha i) (u i) (v i) (hu i) (huv i) (hshort i) x
  have hμ (i : J) : (μ i).real Set.univ ≤ 2 := by
    rw [primeLogCellMeasure_mass]
    exact hmass i
  have hν (i : J) : (ν i).real Set.univ ≤ 2 :=
    primeGiantMeasure_mass_le_two P Q _ _ (hq i) _ _ (hu i) (huv i) (hshort i)
  apply (f'.pullBulk base e).integral_comparison_indexed μ ν hμ hν _
    (fun i => (norm_nonneg _).trans (hs i base))
  intro i y
  have h := hs i (bulkCoordinateInsert base e y)
  change ‖((f'.average (μ i) (e i)).pullBulk base e) y -
    ((f'.average (ν i) (e i)).pullBulk base e) y‖ ≤ _ at h
  simpa only [BulkIntegrand.pullBulk_average] using h

end Ostmann

end OAI
