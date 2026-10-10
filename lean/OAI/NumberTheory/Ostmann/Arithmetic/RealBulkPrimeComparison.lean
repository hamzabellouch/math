import OAI.NumberTheory.Ostmann.Arithmetic.BulkPrimeComparison

namespace OAI

/-! # Bulk-prime comparison with real values in the other coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

noncomputable def realBulkPrimeSmoothSum {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (q a : ℕ) (u v : ℝ) : ℂ :=
  ∑ p ∈ primeLogCellSet q a u v,
    realValueSmoothWeight (Function.update value i p) T ψ X lo hi hlo hhi φ G
      (L.eval (p : ℝ)) (R.eval (p : ℝ)) * ((p : ℝ)⁻¹ : ℂ)

theorem realBulkPrimeSmoothSum_polynomial {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (q a : ℕ) (u v : ℝ) :
    realBulkPrimeSmoothSum value i T L R ψ X lo hi hlo hhi φ G q a u v =
      complexPrimeInterval q a u v (fun y => smoothPolynomialWeight
        (bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) (Real.exp y)) := by
  unfold realBulkPrimeSmoothSum primeLogCellSet complexPrimeInterval
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime ∧ Nat.ModEq q p a
  · rw [ite_eq_left hp, ite_eq_left hp]
    dsimp only
    rw [Real.exp_log (show (0 : ℝ) < p by exact_mod_cast hp.1.pos)]
    rw [bulkSmoothFactors_value value i T hT L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout p]
  · rw [ite_eq_right hp, ite_eq_right hp]

/-- The same comparison allows arbitrary real values in every other bulk slot. The real
integral is the polynomial extension proved equal to the original sampling
expression at every prime, with all endpoint primes retained. -/
theorem PublishedProgressionInput.real_bulk_prime_comparison (P : PublishedProgressionInput)
    {σ : Type*} (value : σ → ℝ) (i : σ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.CompensationAbsent i) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r e : ℕ) (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    let F := bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    let K := (2 ^ n + (T.bulkNodePolynomials value i L R).length) * (2 * (n * d + e) + r)
    ‖realBulkPrimeSmoothSum value i T L R ψ X lo hi hlo hhi φ G q a u v -
      ∫ y in Set.Ioc u v, smoothPolynomialWeight F (Real.exp y) *
        (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      (K + 1 : ℕ) *
        (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)) := by
  dsimp only
  obtain ⟨S, hcard, hroots⟩ := bulkSmoothFactors_root_cuts value i T L R ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip d r e hsize hregular hL hR
  rw [realBulkPrimeSmoothSum_polynomial value i T hT L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout]
  apply (P.smooth_prime_all_roots hQ hq hqQ ha u v hu huv hshort _ S hroots).trans
  have hC := P.errorConstant_nonneg
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul
  · exact_mod_cast Nat.add_le_add_right hcard 1
  · exact bulkSmoothFactors_budget value i T L R ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip
  · exact smoothPolynomialBudget_nonneg _
  · positivity

end Ostmann

end OAI
