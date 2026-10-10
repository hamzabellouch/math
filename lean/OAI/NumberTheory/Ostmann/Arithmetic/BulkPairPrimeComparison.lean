import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogSliceComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelPair

namespace OAI

/-! # The actual conjugate history pair in a bulk-prime slice -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def realValueSmoothPair {σ : Type*} (value : σ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  realValueSmoothWeight value (T false) ψ X lo hi hlo hhi φ G L R *
    conj (realValueSmoothWeight value (T true) ψ X lo hi hlo hhi φ G L R)

noncomputable def bulkPairComparisonBudget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e : ℕ) (B D : ℝ) : ℝ :=
  ((2 * ((2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)) + 1 : ℕ) : ℝ) *
    (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2

/-- Both trees retain their actual shared bulk coordinate. Conjugation doubles
the root budget and squares the smooth budget, without any new analytic input. -/
theorem PublishedProgressionInput.bulk_pair_prime_comparison (P : PublishedProgressionInput)
    {σ : Type*} (value : σ → ℝ) (i : σ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hT : ∀ b, (T b).CompensationAbsent i) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r e : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    let H := fun y => realValueSmoothPair (Function.update value i (Real.exp y)) T
      ψ X lo hi hlo hhi φ G (L.eval (Real.exp y)) (R.eval (Real.exp y))
    ‖complexPrimeInterval q a u v H -
      ∫ y in Set.Ioc u v, H y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        bulkPairComparisonBudget ψ V lo hi n d r e B D * bulkPrimeErrorFactor P Q u := by
  dsimp only
  let F (b : Bool) := bulkSmoothFactors value i (T b) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  let W := movingFourierVariationBudget ψ V lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)
  let K := (2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)
  obtain ⟨S, hS, hrS⟩ := bulkSmoothFactors_root_cuts value i (T false) L R ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip d r e (hsize false) (hregular false) hL hR
  obtain ⟨U, hU, hrU⟩ := bulkSmoothFactors_root_cuts value i (T true) L R ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip d r e (hsize true) (hregular true) hL hR
  have hcard : (S ∪ U).card + 1 ≤ 2 * K + 1 := by
    simp only [MovingSlotData.bulkNodePolynomials_length] at hS hU
    have hc := Finset.card_union_le S U
    dsimp only [K]
    omega
  have hbudget : smoothPolynomialBudget (pairedPolynomialFactors (F false) (F true)) ≤ W ^ 2 := by
    rw [pairedPolynomialFactors_budget, pow_two]
    have h0 := bulkSmoothFactors_budget value i (T false) L R ψ X lo hi V hlo hhi
      (hV false) φ G B D hB hD hφ hlip
    have h1 := bulkSmoothFactors_budget value i (T true) L R ψ X lo hi V hlo hhi
      (hV true) φ G B D hB hD hφ hlip
    exact mul_le_mul h0 h1 (smoothPolynomialBudget_nonneg _) ((smoothPolynomialBudget_nonneg _).trans h0)
  have he (z : ℝ) : smoothPolynomialWeight (pairedPolynomialFactors (F false) (F true)) z =
      realValueSmoothPair (Function.update value i z) T ψ X lo hi hlo hhi φ G (L.eval z) (R.eval z) := by
    rw [pairedPolynomialFactors_weight]
    exact congrArg₂ (fun a b => a * conj b)
      (bulkSmoothFactors_value value i (T false) (hT false) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout z)
      (bulkSmoothFactors_value value i (T true) (hT true) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout z)
  have h := P.smooth_prime_all_roots hQ hq hqQ ha u v hu huv hshort
    (pairedPolynomialFactors (F false) (F true)) (S ∪ U)
    (pairedPolynomialFactors_roots (F false) (F true) S U hrS hrU)
  simp only [he] at h
  apply h.trans
  change ((S ∪ U).card + 1 : ℕ) * smoothPolynomialBudget (pairedPolynomialFactors (F false) (F true)) *
      bulkPrimeErrorFactor P Q u ≤ ((2 * K + 1 : ℕ) : ℝ) * W ^ 2 * bulkPrimeErrorFactor P Q u
  apply mul_le_mul_of_nonneg_right _ (by
    dsimp only [bulkPrimeErrorFactor]
    have := P.errorConstant_nonneg
    positivity)
  exact mul_le_mul (by exact_mod_cast hcard) hbudget (smoothPolynomialBudget_nonneg _) (by positivity)

end Ostmann

end OAI
