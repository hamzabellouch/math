import OAI.NumberTheory.Ostmann.Arithmetic.RealBulkKernelPair
import OAI.NumberTheory.Ostmann.Arithmetic.BulkPrimeCellMass

namespace OAI

/-! # Simultaneous replacement of the full arithmetic bulk kernel -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The full original conjugate pair, including its sharp support conditions, is compared jointly, retaining every Page
correction. The only mass side condition is a finite reciprocal-prime sum. -/
theorem PublishedProgressionInput.bulk_kernel_cells_joint_comparison
    (P : PublishedProgressionInput) {σ C : Type*} [Fintype σ] [Fintype C]
    (base : σ → ℝ) (childBound pivotBound : ℕ → ℕ) (order : List σ) (horder : order.Nodup)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hT : ∀ b i, i ∈ order → (T b).CompensationAbsent i)
    (i₀ : σ) (hi₀ : i₀ ∈ order) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r) (L R : ℝ)
    (Q : ℕ) (hQ : 2 ≤ Q) (q a : σ → C → ℕ) (u v : σ → C → ℝ) (Z : σ → ℝ) (hZ : ∀ i, 0 ≤ Z i)
    (hu : ∀ i c, 1 ≤ u i c) (hq : ∀ i ∈ order, ∀ c, 1 ≤ q i c)
    (hqQ : ∀ i ∈ order, ∀ c, q i c ≤ Q) (ha : ∀ i ∈ order, ∀ c, (a i c).Coprime (q i c))
    (huv : ∀ i ∈ order, ∀ c, u i c ≤ v i c) (hshort : ∀ i ∈ order, ∀ c, v i c ≤ u i c + 1)
    (hmass : ∀ i ∈ order,
      (bulkCellMixture (Z i) (fun c => primeLogCellMeasure (q i c) (a i c) (u i c) (v i c))).real Set.univ ≤ 1)
    (herror : ∀ i ∈ order, Z i * ∑ c, bulkPrimeErrorFactor P Q (u i c) ≤ 1) :
    let f := bulkLogKernelPairIntegrand base order.toFinset childBound pivotBound T
      (fun b i hi => hT b i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
    let μ := fun i c => primeLogCellMeasure (q i c) (a i c) (u i c) (v i c)
    let ν := fun i c => primeGiantMeasure P Q (q i c) (a i c) (u i c) (v i c)
    letI : ∀ i c, IsFiniteMeasure (ν i c) := fun i c =>
      finite_primeGiantMeasure P Q (q i c) (a i c) (u i c) (v i c) (lt_of_lt_of_le zero_lt_one (hu i c))
    ∀ x, ‖f.averages (fun i => bulkCellMixture (Z i) (μ i)) order x -
      f.averages (fun i => bulkCellMixture (Z i) (ν i)) order x‖ ≤
      2 ^ order.length * (order.map (fun i =>
        Z i * ∑ c, bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i c))).sum := by
  let f := bulkLogKernelPairIntegrand base order.toFinset childBound pivotBound T
    (fun b i hi => hT b i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
  let μ := fun i c => primeLogCellMeasure (q i c) (a i c) (u i c) (v i c)
  let ν := fun i c => primeGiantMeasure P Q (q i c) (a i c) (u i c) (v i c)
  let _ : ∀ i c, IsFiniteMeasure (ν i c) := fun i c =>
    finite_primeGiantMeasure P Q (q i c) (a i c) (u i c) (v i c) (lt_of_lt_of_le zero_lt_one (hu i c))
  have hslices (i : σ) (hiMem : i ∈ order) (c : C) (x : σ → ℝ) :
      ‖f.average (μ i c) i x - f.average (ν i c) i x‖ ≤
        bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i c) := by
    exact P.bulk_kernel_log_slice_comparison base order.toFinset childBound pivotBound T i (List.mem_toFinset.mpr hiMem)
      (fun b => hT b i hiMem) ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f
      (fun _ => rfl) hQ (hq i hiMem c) (hqQ i hiMem c) (ha i hiMem c) (u i c) (v i c) (hu i c)
      (huv i hiMem c) (hshort i hiMem c) x
  have hν : ∀ i ∈ order, (bulkCellMixture (Z i) (ν i)).real Set.univ ≤ 2 := by
    intro i hiMem
    exact P.bulk_cell_page_mass_le_two Q hQ (q i) (a i) (u i) (v i)
      (hq i hiMem) (hqQ i hiMem) (ha i hiMem) (hu i) (huv i hiMem) (hshort i hiMem)
      (Z i) (hZ i) (hmass i hiMem) (herror i hiMem)
  exact f.cellMixtures_joint_comparison Z hZ μ ν order horder
    (fun i hiMem => (hmass i hiMem).trans (by norm_num)) hν _
    (fun i hiMem c => (norm_nonneg _).trans (hslices i hiMem c base)) hslices

end Ostmann

end OAI
