import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternIntegrand
import OAI.NumberTheory.Ostmann.Arithmetic.IndexedBulkLogComparison
import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogWeightedNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternNormKernel

namespace OAI

/-! # The actual pattern kernel with its retained bulk logarithmic weights -/

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
    {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

noncomputable def movingPatternLogIntegrand : BulkIntegrand (TreeLeafIndex n × Fin m) :=
  (bulkLogKernelPairIntegrand base (selectedBulkSet (movingPatternBulkEmbedding e slot))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier)
    (movingPatternBulkEmbedding e slot j₀) ((mem_selectedBulkSet _ _).mpr ⟨j₀, rfl⟩)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U).withLogCutoffs base
      (selectedBulkSet (movingPatternBulkEmbedding e slot)) cb logSlots |>.pullBulk base (movingPatternBulkEmbedding e slot)

theorem movingPatternLogIntegrand_norm_le (z : (TreeLeafIndex n × Fin m) → ℝ) :
    ‖movingPatternLogIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb z‖ ≤
    ‖movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U z‖ :=
  BulkIntegrand.withLogCutoffs_norm_le _ base
    (selectedBulkSet (movingPatternBulkEmbedding e slot)) cb logSlots
    (bulkCoordinateInsert base (movingPatternBulkEmbedding e slot) z)

theorem movingPatternLogIntegrand_norm (z : (TreeLeafIndex n × Fin m) → ℝ) :
    ‖movingPatternLogIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb z‖ ≤
    (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  apply le_trans (BulkIntegrand.withLogCutoffs_norm_le _ base
    (selectedBulkSet (movingPatternBulkEmbedding e slot)) cb logSlots
    (bulkCoordinateInsert base (movingPatternBulkEmbedding e slot) z))
  exact movingPatternBulkIntegrand_norm e tierB tierC t small slot perm pattern hB htier base
    childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U z

theorem movingPatternLogIntegrand_norm_window (z : (TreeLeafIndex n × Fin m) → ℝ) :
    ‖movingPatternLogIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb z‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2 :=
  (movingPatternLogIntegrand_norm_le e tierB tierC t small slot perm pattern hB htier base
    childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb z).trans
      (movingPatternBulkIntegrand_norm_window e tierB tierC t small slot perm pattern hB htier base
        childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U z)

theorem movingPatternLogIntegrand_nat
    (base₀ value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base₀ i)
    (hvalue : ∀ i, value i ≠ 0)
    (hf : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    movingPatternLogIntegrand e tierB tierC t small slot perm pattern hB htier
      (fun i => (base₀ i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
      φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb
      (fun j => Real.log (value (movingPatternBulkEmbedding e slot j) : ℝ)) =
    ((∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
      movingRealKernelPair value T
        (fun b => (T b).formulaNodes value hvalue childBound pivotBound
          (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hf b)
          (.prime false) (.prime true)) ψ X lo hi hlo hhi φ G L U := by
  dsimp only
  change ((_ : ℝ) : ℂ) * realValueKernelPair _ childBound pivotBound _
    ψ X lo hi hlo hhi φ G L U = _
  rw [selectedBulkLogValues_nat base₀ value (movingPatternBulkEmbedding e slot) hv
    (fun j => Nat.pos_of_ne_zero (hvalue _))]
  rw [realValueKernelPair_nat value hvalue childBound pivotBound _
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hf)]

theorem PublishedProgressionInput.movingPatternLogIntegrand_comparison
    (P : PublishedProgressionInput) {r₀ : ℕ}
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (rlog : ℕ) (hslots : ∀ j, (logSlots j).length ≤ rlog)
    {Q : ℕ} (hQ : 2 ≤ Q)
    (q a : TreeLeafIndex n × Fin m → ℕ) (u v : TreeLeafIndex n × Fin m → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let K := movingPatternLogIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb
    ‖(∫ z, K z ∂Measure.pi (fun i => primeLogCellMeasure (q i) (a i) (u i) (v i))) -
      ∫ z, K z ∂Measure.pi (fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i))‖ ≤
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ i,
        bulkLogWeightedKernelPairBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0
          tlog rlog Bφ Dφ Dlog * bulkPrimeErrorFactor P Q (u i) := by
  let f := bulkLogKernelPairIntegrand base (selectedBulkSet (movingPatternBulkEmbedding e slot))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier)
    (movingPatternBulkEmbedding e slot j₀)
    ((mem_selectedBulkSet _ _).mpr ⟨j₀, rfl⟩) ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
  exact P.bulk_log_weighted_integral_comparison_indexed base
    (selectedBulkSet (movingPatternBulkEmbedding e slot)) (movingPatternBulkEmbedding e slot)
    (fun j => (mem_selectedBulkSet _ _).mpr ⟨j, rfl⟩) childBound pivotBound
    (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout _ _
    (movingPatternFinBulkData_size e t small slot perm pattern hsmall)
    (movingPatternFinBulkData_regular_length e t small slot perm pattern hsmall)
    L U f (fun _ => rfl) logSlots cb Dlog hDlog hloglip rlog hslots
    hQ q a u v hq hqQ ha hu huv hshort hmass

end
end Ostmann

end OAI
