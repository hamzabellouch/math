import OAI.NumberTheory.Ostmann.Arithmetic.RealBulkKernelPair

namespace OAI

/-! # Simultaneous replacement of the full arithmetic bulk kernel -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The full original conjugate pair, including its sharp support conditions, is compared jointly, retaining every Page
correction. The only mass side condition is a finite reciprocal-prime sum. -/
theorem PublishedProgressionInput.bulk_kernel_log_joint_comparison
    (P : PublishedProgressionInput) {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (childBound pivotBound : ℕ → ℕ) (order : List σ) (horder : order.Nodup)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hT : ∀ b i, i ∈ order → (T b).CompensationAbsent i)
    (i₀ : σ) (hi₀ : i₀ ∈ order) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r) (L R : ℝ)
    (Q : ℕ) (hQ : 2 ≤ Q) (q a : σ → ℕ) (u v : σ → ℝ)
    (hu : ∀ i, 1 ≤ u i) (hq : ∀ i ∈ order, 1 ≤ q i)
    (hqQ : ∀ i ∈ order, q i ≤ Q) (ha : ∀ i ∈ order, (a i).Coprime (q i))
    (huv : ∀ i ∈ order, u i ≤ v i) (hshort : ∀ i ∈ order, v i ≤ u i + 1)
    (hmass : ∀ i ∈ order, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let f := bulkLogKernelPairIntegrand base order.toFinset childBound pivotBound T
      (fun b i hi => hT b i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
    let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
    let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
    letI : ∀ i, IsFiniteMeasure (ν i) := fun i =>
      finite_primeGiantMeasure P Q (q i) (a i) (u i) (v i) (lt_of_lt_of_le zero_lt_one (hu i))
    ∀ x, ‖f.averages μ order x - f.averages ν order x‖ ≤
      2 ^ order.length * (order.map (fun i =>
        bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i))).sum := by
  let f := bulkLogKernelPairIntegrand base order.toFinset childBound pivotBound T
    (fun b i hi => hT b i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
  let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
  let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
  let _ : ∀ i, IsFiniteMeasure (ν i) := fun i =>
    finite_primeGiantMeasure P Q (q i) (a i) (u i) (v i) (lt_of_lt_of_le zero_lt_one (hu i))
  have hslices (i : σ) (hiMem : i ∈ order) (x : σ → ℝ) :
      ‖f.average (μ i) i x - f.average (ν i) i x‖ ≤
        bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i) := by
    exact P.bulk_kernel_log_slice_comparison base order.toFinset childBound pivotBound T i (List.mem_toFinset.mpr hiMem)
      (fun b => hT b i hiMem) ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f
      (fun _ => rfl) hQ (hq i hiMem) (hqQ i hiMem) (ha i hiMem) (u i) (v i) (hu i)
      (huv i hiMem) (hshort i hiMem) x
  have hμ : ∀ i ∈ order, (μ i).real Set.univ ≤ 2 := by
    intro i hiMem
    change (primeLogCellMeasure (q i) (a i) (u i) (v i)).real Set.univ ≤ 2
    rw [primeLogCellMeasure_mass]
    exact hmass i hiMem
  have hν : ∀ i ∈ order, (ν i).real Set.univ ≤ 2 := by
    intro i hiMem
    exact primeGiantMeasure_mass_le_two P Q (q i) (a i) (hq i hiMem) (u i) (v i)
      (hu i) (huv i hiMem) (hshort i hiMem)
  exact BulkIntegrand.averages_comparison μ ν order horder hμ hν f _
    (fun i hiMem => (norm_nonneg _).trans (hslices i hiMem base)) hslices

end Ostmann

end OAI
