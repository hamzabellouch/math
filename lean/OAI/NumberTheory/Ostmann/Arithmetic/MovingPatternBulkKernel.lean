import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkLog
import OAI.NumberTheory.Ostmann.Arithmetic.IndexedBulkKernelComparison

namespace OAI

/-! # Prime-to-Page comparison for the actual pattern's sharp bulk kernel -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The sharp real kernel is constructed here. Compensation independence,
all frequency bounds and both polynomial length budgets come from the actual
pattern constructor, including its prescribed bulk permutation. -/
theorem PublishedProgressionInput.movingPattern_kernel_integral_comparison
    (P : PublishedProgressionInput) {B C : Type*} {N n m r₀ : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (base : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ)
    {Q : ℕ} (hQ : 2 ≤ Q)
    (q a : TreeLeafIndex n × Fin m → ℕ) (u v : TreeLeafIndex n × Fin m → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let lift := movingPatternBulkEmbedding e slot
    let S := selectedBulkSet lift
    let hcomp := movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier
    let hV := movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq
    let f := bulkLogKernelPairIntegrand base S childBound pivotBound T hcomp
      (lift j₀) ((mem_selectedBulkSet lift _).mpr ⟨j₀, rfl⟩)
      ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hout L R
    let K := f.pullBulk base lift
    ‖(∫ y, K y ∂Measure.pi (fun i => primeLogCellMeasure (q i) (a i) (u i) (v i))) -
      ∫ y, K y ∂Measure.pi (fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i))‖ ≤
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) *
        ∑ i, bulkKernelPairComparisonBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
          bulkPrimeErrorFactor P Q (u i) := by
  dsimp only
  let f := bulkLogKernelPairIntegrand base (selectedBulkSet (movingPatternBulkEmbedding e slot))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier)
    (movingPatternBulkEmbedding e slot j₀)
    ((mem_selectedBulkSet _ _).mpr ⟨j₀, rfl⟩) ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L R
  exact P.bulk_kernel_integral_comparison_indexed base
    (selectedBulkSet (movingPatternBulkEmbedding e slot)) (movingPatternBulkEmbedding e slot)
    (fun j => (mem_selectedBulkSet _ _).mpr ⟨j, rfl⟩) childBound pivotBound
    (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout _ _
    (movingPatternFinBulkData_size e t small slot perm pattern hsmall)
    (movingPatternFinBulkData_regular_length e t small slot perm pattern hsmall)
    L R f (fun _ => rfl) hQ q a u v hq hqQ ha hu huv hshort hmass

end Ostmann

end OAI
