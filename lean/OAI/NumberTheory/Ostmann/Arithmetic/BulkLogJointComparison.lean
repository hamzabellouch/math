import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogSliceComparison

namespace OAI

/-! # Joint replacement of the original bulk-prime samples

Every slice error is derived from the published progression estimate. The
commuting coordinate averages give the full product comparison with the
retained Page measures; no independence of a conditionally sampled weight is
assumed.
-/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap BoundedContinuousFunction

/-- Product comparison for the actual smooth tree, on arbitrary distinct bulk
coordinates and arbitrary residue cells. -/
theorem PublishedProgressionInput.bulk_log_joint_comparison
    (P : PublishedProgressionInput) {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (order : List σ) (horder : order.Nodup)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ order, T.CompensationAbsent i)
    (i₀ : σ) (hi₀ : i₀ ∈ order) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r) (L R : ℝ)
    (Q : ℕ) (hQ : 2 ≤ Q) (q a : σ → ℕ) (u v : σ → ℝ)
    (hu : ∀ i, 1 ≤ u i) (hq : ∀ i ∈ order, 1 ≤ q i)
    (hqQ : ∀ i ∈ order, q i ≤ Q) (ha : ∀ i ∈ order, (a i).Coprime (q i))
    (huv : ∀ i ∈ order, u i ≤ v i) (hshort : ∀ i ∈ order, v i ≤ u i + 1)
    (hmass : ∀ i ∈ order, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let f := bulkLogSmoothFunction base order.toFinset T
      (fun i hi => hT i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
    let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
    let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
    letI : ∀ i, IsFiniteMeasure (ν i) := fun i =>
      finite_primeGiantMeasure P Q (q i) (a i) (u i) (v i) (lt_of_lt_of_le zero_lt_one (hu i))
    ‖coordinateAverages μ order f - coordinateAverages ν order f‖ ≤
      2 ^ order.length * (order.map (fun i =>
        bulkSmoothComparisonBudget ψ V lo hi n d r B D * bulkPrimeErrorFactor P Q (u i))).sum := by
  let f := bulkLogSmoothFunction base order.toFinset T
    (fun i hi => hT i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
  let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
  let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
  let _ : ∀ i, IsFiniteMeasure (ν i) := fun i =>
    finite_primeGiantMeasure P Q (q i) (a i) (u i) (v i) (lt_of_lt_of_le zero_lt_one (hu i))
  have hslices (i : σ) (hiMem : i ∈ order) :
      ‖coordinateAverage (μ i) i f - coordinateAverage (ν i) i f‖ ≤
        bulkSmoothComparisonBudget ψ V lo hi n d r B D * bulkPrimeErrorFactor P Q (u i) := by
    exact P.bulk_log_slice_comparison base order.toFinset T i (List.mem_toFinset.mpr hiMem)
      (hT i hiMem) ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f
      (fun _ => rfl) hQ (hq i hiMem) (hqQ i hiMem) (ha i hiMem) (u i) (v i) (hu i) (huv i hiMem) (hshort i hiMem)
  apply coordinateAverages_comparison μ ν order horder
  · intro i hi
    change (primeLogCellMeasure (q i) (a i) (u i) (v i)).real Set.univ ≤ 2
    rw [primeLogCellMeasure_mass]
    exact hmass i hi
  · intro i hi
    exact primeGiantMeasure_mass_le_two P Q (q i) (a i) (hq i hi) (u i) (v i)
      (hu i) (huv i hi) (hshort i hi)
  · intro i hi
    exact (norm_nonneg _).trans (hslices i hi)
  · exact hslices

end Ostmann

end OAI
