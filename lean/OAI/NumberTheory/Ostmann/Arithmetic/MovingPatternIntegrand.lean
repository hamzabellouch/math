import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternKernelNorm

namespace OAI

/-! # The actual pattern's bounded bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

noncomputable def movingPatternBulkIntegrand : BulkIntegrand (TreeLeafIndex n × Fin m) :=
  (bulkLogKernelPairIntegrand base (selectedBulkSet (movingPatternBulkEmbedding e slot))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier)
    (movingPatternBulkEmbedding e slot j₀) ((mem_selectedBulkSet _ _).mpr ⟨j₀, rfl⟩)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U).pullBulk base (movingPatternBulkEmbedding e slot)

theorem movingPatternBulkIntegrand_norm (z : (TreeLeafIndex n × Fin m) → ℝ) :
    ‖movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U z‖ ≤
    (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 :=
  movingPattern_kernel_norm_le e tierB tierC t small slot perm pattern hB htier
    (bulkLogValues base (selectedBulkSet (movingPatternBulkEmbedding e slot))
      (bulkCoordinateInsert base (movingPatternBulkEmbedding e slot) z))
    childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U

theorem movingPatternBulkIntegrand_nat
    (base₀ value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base₀ i)
    (hvalue : ∀ i, value i ≠ 0)
    (hf : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier
      (fun i => (base₀ i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
      φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
      (fun j => Real.log (value (movingPatternBulkEmbedding e slot j) : ℝ)) =
    movingRealKernelPair value T
      (fun b => (T b).formulaNodes value hvalue childBound pivotBound
        (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hf b)
        (.prime false) (.prime true)) ψ X lo hi hlo hhi φ G L U :=
  movingPattern_bulk_kernel_nat e t small slot perm pattern base₀ value hv hvalue
    childBound pivotBound hf ψ X lo hi hlo hhi φ G L U

theorem PublishedProgressionInput.movingPatternBulkIntegrand_comparison
    (P : PublishedProgressionInput) {r₀ : ℕ}
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀)
    {Q : ℕ} (hQ : 2 ≤ Q)
    (q a : TreeLeafIndex n × Fin m → ℕ) (u v : TreeLeafIndex n × Fin m → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let K := movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
    ‖(∫ z, K z ∂Measure.pi (fun i => primeLogCellMeasure (q i) (a i) (u i) (v i))) -
      ∫ z, K z ∂Measure.pi (fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i))‖ ≤
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ i,
        bulkKernelPairComparisonBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
          bulkPrimeErrorFactor P Q (u i) :=
  P.movingPattern_kernel_integral_comparison e tierB tierC t small slot perm pattern hB htier hsmall
    base childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
    hQ q a u v hq hqQ ha hu huv hshort hmass

end
end Ostmann

end OAI
