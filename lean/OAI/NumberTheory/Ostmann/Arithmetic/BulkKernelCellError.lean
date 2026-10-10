import OAI.NumberTheory.Ostmann.Arithmetic.BulkWeightedCellComparison

namespace OAI

/-! # The explicit published-input error for all original residue cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.bulk_kernel_weighted_cells_comparison
    (P : PublishedProgressionInput) {σ C : Type*} [Fintype σ] [Fintype C] {k n : ℕ}
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
    (Q M : ℕ) [NeZero M] (hQ : 2 ≤ Q) (hM : M ≤ Q)
    (u v : Fin k → C → ℝ) (hu : ∀ i c, 1 ≤ u i c)
    (huv : ∀ i c, u i c ≤ v i c) (hshort : ∀ i c, v i c ≤ u i c + 1)
    (hmass : ∀ i c (a : (ZMod M)ˣ),
      ∑ p ∈ primeLogCellSet M a.val.val (u i c) (v i c), (p : ℝ)⁻¹ ≤ 2)
    (Z : Fin k → ℝ) (hZ : ∀ i, 0 ≤ Z i)
    (a : (Fin k → (ZMod M)ˣ) → ℂ) :
    let K := f.pullBulk base e
    let E := fun c : Fin k → C => 2 ^ k * ∑ i,
      bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i (c i))
    ‖((∏ i, Z i : ℝ) : ℂ) * ∑ c : Fin k → C, ∑ z : Fin k → (ZMod M)ˣ,
        ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun i =>
          primeLogCellMeasure M (z i).val.val (u i (c i)) (v i (c i))) -
      ((∏ i, Z i : ℝ) : ℂ) * ∑ c : Fin k → C, ∑ z : Fin k → (ZMod M)ˣ,
        ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun i =>
          primeGiantMeasure P Q M (z i).val.val (u i (c i)) (v i (c i)))‖ ≤
      (∏ i, Z i) * ∑ c : Fin k → C, ∑ z, ‖a z‖ * E c := by
  let μ := fun (c : Fin k → C) (z : Fin k → (ZMod M)ˣ) i =>
    primeLogCellMeasure M (z i).val.val (u i (c i)) (v i (c i))
  let ν := fun (c : Fin k → C) (z : Fin k → (ZMod M)ˣ) i =>
    primeGiantMeasure P Q M (z i).val.val (u i (c i)) (v i (c i))
  let _ : ∀ c z i, IsFiniteMeasure (ν c z i) := fun c z i =>
    finite_primeGiantMeasure P Q _ _ _ _ (lt_of_lt_of_le zero_lt_one (hu i (c i)))
  let E := fun c : Fin k → C => 2 ^ k * ∑ i,
    bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i (c i))
  have herr (c : Fin k → C) (z : Fin k → (ZMod M)ˣ) :
      ‖(∫ y, (f.pullBulk base e) y ∂Measure.pi (μ c z)) -
        ∫ y, (f.pullBulk base e) y ∂Measure.pi (ν c z)‖ ≤ E c := by
    exact P.bulk_kernel_integral_comparison base S e he childBound pivotBound T hT
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f hf
      hQ (fun _ => M) (fun i => (z i).val.val) (fun i => u i (c i)) (fun i => v i (c i))
      (fun _ => Nat.pos_of_ne_zero (NeZero.ne M)) (fun _ => hM)
      (fun i => ZMod.val_coe_unit_coprime (z i))
      (fun i => hu i (c i)) (fun i => huv i (c i)) (fun i => hshort i (c i))
      (fun i => hmass i (c i) (z i))

  have h := bulk_weighted_cell_comparison (f.pullBulk base e) a Z hZ μ ν
    (fun c _ => E c) herr
  dsimp only [μ, ν, E] at h ⊢
  simp only [finite_univ_canonical] at h ⊢
  exact h

end Ostmann

end OAI
