import OAI.NumberTheory.Ostmann.Arithmetic.BulkKernelCellComparison
import OAI.NumberTheory.Ostmann.Construction.OriginalPrimeCellExpectation

namespace OAI

/-! # The full bulk kernel comparison under its original finite prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- Joint prime-to-Page replacement for the full sharp paired kernel, inside
the original product-prior expectation. The original harmonic normalizations
are used on both sides and the interval theorem supplies every Page mass bound. -/
theorem PublishedProgressionInput.original_kernel_comparison
    (P : PublishedProgressionInput) {σ C : Type*} [Fintype σ] [Fintype C]
    (P₀ : Finset ℕ) (base : σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (order : List σ) (horder : order.Nodup)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hT : ∀ b i, i ∈ order → (T b).CompensationAbsent i)
    (i₀ : σ) (hi₀ : i₀ ∈ order) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r) (L R : ℝ)
    (Q : ℕ) (hQ : 2 ≤ Q) (q : σ → ℕ) (a : σ → C → ℕ) (u v : σ → C → ℝ)
    (hSP : ∀ i, primeCellSupport (q i) (a i) (u i) (v i) ⊆ P₀)
    (hsep : ∀ i c e, c ≠ e →
      ¬Nat.ModEq (q i) (a i c) (a i e) ∨ v i c ≤ u i e ∨ v i e ≤ u i c)
    (hS : ∀ i, (∑ p ∈ primeCellSupport (q i) (a i) (u i) (v i), (p : ℝ)⁻¹) ≠ 0)
    (hu : ∀ i c, 1 ≤ u i c) (hq : ∀ i ∈ order, 1 ≤ q i)
    (hqQ : ∀ i ∈ order, q i ≤ Q) (ha : ∀ i ∈ order, ∀ c, (a i c).Coprime (q i))
    (huv : ∀ i ∈ order, ∀ c, u i c ≤ v i c) (hshort : ∀ i ∈ order, ∀ c, v i c ≤ u i c + 1)
    (herror : ∀ i ∈ order,
      (∑ p ∈ primeCellSupport (q i) (a i) (u i) (v i), (p : ℝ)⁻¹)⁻¹ *
        ∑ c, bulkPrimeErrorFactor P Q (u i c) ≤ 1) :
    let S := fun i => primeCellSupport (q i) (a i) (u i) (v i)
    let Z := fun i => (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹
    let f := bulkLogKernelPairIntegrand base order.toFinset childBound pivotBound T
      (fun b i hi => hT b i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
    let ν := fun i => bulkCellMixture (Z i)
      (fun c => primeGiantMeasure P Q (q i) (a i c) (u i c) (v i c))
    letI : ∀ i c, IsFiniteMeasure (primeGiantMeasure P Q (q i) (a i c) (u i c) (v i c)) :=
      fun i c => finite_primeGiantMeasure P Q (q i) (a i c) (u i c) (v i c)
        (lt_of_lt_of_le zero_lt_one (hu i c))
    ‖(∑ x : σ → P₀, ((∏ i, primeSubsetPrior P₀ (S i) (x i) : ℝ) : ℂ) * f (primeArrayLogs x)) -
      ∑ x : σ → P₀, ((∏ i, primeSubsetPrior P₀ (S i) (x i) : ℝ) : ℂ) *
        f.averages ν order (primeArrayLogs x)‖ ≤
      2 ^ order.length * (order.map (fun i => Z i *
        ∑ c, bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i c))).sum := by
  let S := fun i => primeCellSupport (q i) (a i) (u i) (v i)
  let Z := fun i => (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹
  let f := bulkLogKernelPairIntegrand base order.toFinset childBound pivotBound T
    (fun b i hi => hT b i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
  let ν := fun i => bulkCellMixture (Z i)
    (fun c => primeGiantMeasure P Q (q i) (a i c) (u i c) (v i c))
  let _ : ∀ i c, IsFiniteMeasure (primeGiantMeasure P Q (q i) (a i c) (u i c) (v i c)) :=
    fun i c => finite_primeGiantMeasure P Q (q i) (a i c) (u i c) (v i c)
      (lt_of_lt_of_le zero_lt_one (hu i c))
  have hZ (i : σ) : 0 ≤ Z i := inv_nonneg.mpr (Finset.sum_nonneg fun p _ => by positivity)
  have hm (i : σ) (_hi : i ∈ order) :
      (bulkCellMixture (Z i) (fun c => primeLogCellMeasure (q i) (a i c) (u i c) (v i c))).real Set.univ ≤ 1 := by
    rw [bulkPrimeCells_normalized (q i) (a i) (u i) (v i) (hsep i) (hS i)]
  have hp := P.bulk_kernel_cells_joint_comparison base childBound pivotBound order horder T hT i₀ hi₀
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R Q hQ
    (fun i _ => q i) a u v Z hZ hu (fun i hi _ => hq i hi) (fun i hi _ => hqQ i hi)
    ha huv hshort hm herror
  exact f.originalPrimeCells_mean_comparison P₀ q a u v hSP hsep hS order ν _ hp

end Ostmann

end OAI
