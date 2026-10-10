import Mathlib.Topology.ContinuousMap.Bounded.Star
import OAI.NumberTheory.Ostmann.Arithmetic.BulkPairPrimeComparison
import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogJointComparison

namespace OAI

/-! # Simultaneous prime replacement for the actual conjugate history pair -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate BoundedContinuousFunction

noncomputable def bulkLogSmoothPairFunction {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hT : ∀ b i, i ∈ S → (T b).CompensationAbsent i) (i : σ) (hiS : i ∈ S)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) : (σ → ℝ) →ᵇ ℂ :=
  bulkLogSmoothFunction base S (T false) (hT false) i hiS ψ X lo hi V hlo hhi (hV false)
    φ G B D hB hD hφ hlip hout L R *
    star (bulkLogSmoothFunction base S (T true) (hT true) i hiS ψ X lo hi V hlo hhi (hV true)
      φ G B D hB hD hφ hlip hout L R)

theorem PublishedProgressionInput.bulk_log_pair_slice_comparison
    (P : PublishedProgressionInput) {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (S : Finset σ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (i : σ) (hiS : i ∈ S) (hT : ∀ b, (T b).CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r)
    (L R : ℝ) (f : (σ → ℝ) →ᵇ ℂ)
    (hf : ∀ x, f x = realValueSmoothPair (bulkLogValues base S x) T ψ X lo hi hlo hhi φ G L R)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    letI := finite_primeGiantMeasure P Q q a u v (lt_of_lt_of_le zero_lt_one hu)
    ‖coordinateAverage (primeLogCellMeasure q a u v) i f -
      coordinateAverage (primeGiantMeasure P Q q a u v) i f‖ ≤
        bulkPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q u := by
  let _ := finite_primeGiantMeasure P Q q a u v (lt_of_lt_of_le zero_lt_one hu)
  have hpoint (x : σ → ℝ) :
      ‖coordinateAverage (primeLogCellMeasure q a u v) i f x -
        coordinateAverage (primeGiantMeasure P Q q a u v) i f x‖ ≤
          bulkPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q u := by
    let value := bulkLogValues base S x
    let H := fun y => realValueSmoothPair (Function.update value i (Real.exp y)) T
      ψ X lo hi hlo hhi φ G L R
    have hprime : coordinateAverage (primeLogCellMeasure q a u v) i f x =
        complexPrimeInterval q a u v H := by
      rw [coordinateAverage_apply]
      change (∫ t, coordinateSlice f i x t ∂primeLogCellMeasure q a u v) = _
      rw [primeLogCellMeasure_integral]
      unfold primeLogCellSet complexPrimeInterval
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.Prime ∧ Nat.ModEq q p a
      · rw [ite_eq_left hp, ite_eq_left hp]
        change f (Function.update x i (Real.log p)) * _ = H (Real.log p) * _
        rw [hf, bulkLogValues_update base S x i hiS]
      · rw [ite_eq_right hp, ite_eq_right hp]
    have hpage : coordinateAverage (primeGiantMeasure P Q q a u v) i f x =
        ∫ y in Set.Ioc u v, H y * (selectedPrimeLogDensity P Q q a y : ℂ) := by
      rw [coordinateAverage_apply, primeGiantMeasure_integral P Q q a u v (by linarith)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y _
      dsimp only
      rw [hf, bulkLogValues_update base S x i hiS]
    rw [hprime, hpage]
    have h := P.bulk_pair_prime_comparison value i T hT (Polynomial.C L) (Polynomial.C R)
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r 0 hsize hregular
      (by simp) (by simp) hQ hq hqQ ha u v hu huv hshort
    simpa only [Polynomial.eval_C] using h
  exact (BoundedContinuousFunction.norm_le ((norm_nonneg _).trans (hpoint (fun _ => 0)))).mpr hpoint

/-- The original conjugate pair is compared jointly, retaining every Page
correction. The only mass side condition is a finite reciprocal-prime sum. -/
theorem PublishedProgressionInput.bulk_log_pair_joint_comparison
    (P : PublishedProgressionInput) {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (order : List σ) (horder : order.Nodup)
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
    let f := bulkLogSmoothPairFunction base order.toFinset T
      (fun b i hi => hT b i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
    let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
    let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
    letI : ∀ i, IsFiniteMeasure (ν i) := fun i =>
      finite_primeGiantMeasure P Q (q i) (a i) (u i) (v i) (lt_of_lt_of_le zero_lt_one (hu i))
    ‖coordinateAverages μ order f - coordinateAverages ν order f‖ ≤
      2 ^ order.length * (order.map (fun i =>
        bulkPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i))).sum := by
  let f := bulkLogSmoothPairFunction base order.toFinset T
    (fun b i hi => hT b i (List.mem_toFinset.mp hi)) i₀ (List.mem_toFinset.mpr hi₀)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
  let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
  let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
  let _ : ∀ i, IsFiniteMeasure (ν i) := fun i =>
    finite_primeGiantMeasure P Q (q i) (a i) (u i) (v i) (lt_of_lt_of_le zero_lt_one (hu i))
  have hslices (i : σ) (hiMem : i ∈ order) :
      ‖coordinateAverage (μ i) i f - coordinateAverage (ν i) i f‖ ≤
        bulkPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q (u i) := by
    exact P.bulk_log_pair_slice_comparison base order.toFinset T i (List.mem_toFinset.mpr hiMem)
      (fun b => hT b i hiMem) ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f
      (fun _ => rfl) hQ (hq i hiMem) (hqQ i hiMem) (ha i hiMem) (u i) (v i) (hu i)
      (huv i hiMem) (hshort i hiMem)
  apply coordinateAverages_comparison μ ν order horder
  · intro i hiMem
    change (primeLogCellMeasure (q i) (a i) (u i) (v i)).real Set.univ ≤ 2
    rw [primeLogCellMeasure_mass]
    exact hmass i hiMem
  · intro i hiMem
    exact primeGiantMeasure_mass_le_two P Q (q i) (a i) (hq i hiMem) (u i) (v i)
      (hu i) (huv i hiMem) (hshort i hiMem)
  · intro i hiMem
    exact (norm_nonneg _).trans (hslices i hiMem)
  · exact hslices

end Ostmann

end OAI
