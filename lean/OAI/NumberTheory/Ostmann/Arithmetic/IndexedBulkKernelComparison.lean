import OAI.NumberTheory.Ostmann.Arithmetic.BulkKernelIntegralComparison
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCoordinateEnumeration

namespace OAI

/-! # The sharp-kernel comparison in the original tree-and-word coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem BulkIntegrand.averages_enum {J : Type*} [Fintype J] {k : ℕ}
    (f : BulkIntegrand J) (g : Fin k ≃ J)
    (μ : J → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (x : J → ℝ) :
    f.averages μ ((List.finRange k).map g) x = ∫ y, f y ∂Measure.pi μ := by
  have he (y : J → ℝ) : bulkCoordinateInsert (fun _ : J => (0 : ℝ)) (Function.Embedding.refl J) y = y := by
    funext j
    exact bulkCoordinateInsert_at _ (Function.Embedding.refl J) y j
  have h := f.selected_bulk_integral_enum (fun _ => 0) (Function.Embedding.refl J) g μ x
  simpa only [Function.Embedding.refl_apply, he] using h

theorem BulkIntegrand.integral_comparison_indexed {J : Type*} [Fintype J]
    (f : BulkIntegrand J) (μ ν : J → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (hμ : ∀ i, (μ i).real Set.univ ≤ 2) (hν : ∀ i, (ν i).real Set.univ ≤ 2)
    (ε : J → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (herr : ∀ i x, ‖f.average (μ i) i x - f.average (ν i) i x‖ ≤ ε i) :
    ‖(∫ x, f x ∂Measure.pi μ) - ∫ x, f x ∂Measure.pi ν‖ ≤
      2 ^ Fintype.card J * ∑ i, ε i := by
  let g := (Fintype.equivFin J).symm
  have hn : ((List.finRange (Fintype.card J)).map g).Nodup :=
    (List.nodup_finRange _).map g.injective
  have h := f.averages_comparison μ ν _ hn (fun i _ => hμ i) (fun i _ => hν i)
    ε (fun i _ => hε i) (fun i _ => herr i) (fun _ => 0)
  rw [f.averages_enum g, f.averages_enum g] at h
  have hs : (((List.finRange (Fintype.card J)).map g).map ε).sum = ∑ i, ε i := by
    rw [List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
    exact g.sum_comp ε
  simpa only [List.length_map, List.length_finRange, hs] using h

theorem PublishedProgressionInput.bulk_kernel_integral_comparison_indexed
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
    {Q : ℕ} (hQ : 2 ≤ Q) (q a : J → ℕ) (u v : J → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
    let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
    ‖(∫ y, f (bulkCoordinateInsert base e y) ∂Measure.pi μ) -
      ∫ y, f (bulkCoordinateInsert base e y) ∂Measure.pi ν‖ ≤
      2 ^ Fintype.card J * ∑ i, bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D *
        bulkPrimeErrorFactor P Q (u i) := by
  let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
  let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
  let _ : ∀ i, IsFiniteMeasure (ν i) := fun i =>
    finite_primeGiantMeasure P Q _ _ _ _ (lt_of_lt_of_le zero_lt_one (hu i))
  have hs (i : J) (x : σ → ℝ) := P.bulk_kernel_log_slice_comparison
    base S childBound pivotBound T (e i) (he i) (fun b => hT b i)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f hf
    hQ (hq i) (hqQ i) (ha i) (u i) (v i) (hu i) (huv i) (hshort i) x
  have hμ (i : J) : (μ i).real Set.univ ≤ 2 := by
    rw [primeLogCellMeasure_mass]
    exact hmass i
  have hν (i : J) : (ν i).real Set.univ ≤ 2 :=
    primeGiantMeasure_mass_le_two P Q _ _ (hq i) _ _ (hu i) (huv i) (hshort i)
  apply (f.pullBulk base e).integral_comparison_indexed μ ν hμ hν _
    (fun i => (norm_nonneg _).trans (hs i base))
  intro i y
  have h := hs i (bulkCoordinateInsert base e y)
  change ‖((f.average (μ i) (e i)).pullBulk base e) y -
    ((f.average (ν i) (e i)).pullBulk base e) y‖ ≤ _ at h
  simpa only [BulkIntegrand.pullBulk_average] using h

end Ostmann

end OAI
