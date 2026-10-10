import OAI.NumberTheory.Ostmann.Arithmetic.BulkKernelPairComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogFactors

namespace OAI

/-! # Joint prime comparison retaining the initial bulk logarithmic cutoffs -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def bulkLogWeightedKernelPairBudget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e t rlog : ℕ) (B D Dlog : ℝ) : ℝ :=
  ((2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)) +
      ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r))) + t * rlog + 1 : ℕ) : ℝ) *
    ((movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 *
      (2 + Dlog * (Real.exp 2 - 1)) ^ t)

/-- The signed pair keeps every initial bulk log-sum factor. Its additional
root and variation costs are explicit, and independent of the prime values. -/
theorem PublishedProgressionInput.bulk_log_weighted_kernel_pair_prime_comparison (P : PublishedProgressionInput)
    {σ : Type*} (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hT : ∀ b, (T b).CompensationAbsent i)
    (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r e : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e)
    {t : ℕ} (slots : Fin t → List σ) (cb Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (rlog : ℕ) (hslots : ∀ j, (slots j).length ≤ rlog)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    let H := fun y => ((∏ j, bulkLogCutoffWeight
      (Function.update value i (Real.exp y)) cb (slots j) : ℝ) : ℂ) * realValueKernelPair (Function.update value i (Real.exp y)) childBound pivotBound T
      ψ X lo hi hlo hhi φ G (L.eval (Real.exp y)) (R.eval (Real.exp y))
    ‖complexPrimeInterval q a u v H -
      ∫ y in Set.Ioc u v, H y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        bulkLogWeightedKernelPairBudget ψ V lo hi n d r e t rlog B D Dlog * bulkPrimeErrorFactor P Q u := by
  dsimp only
  let F (b : Bool) := bulkSmoothFactors value i (T b) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  let W := movingFourierVariationBudget ψ V lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)
  let A := (2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)
  let B' := (3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r)
  obtain ⟨S, hS, hrS⟩ := bulkSmoothFactors_root_cuts value i (T false) L R ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip d r e (hsize false) (hregular false) hL hR
  obtain ⟨U, hU, hrU⟩ := bulkSmoothFactors_root_cuts value i (T true) L R ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip d r e (hsize true) (hregular true) hL hR
  obtain ⟨S', hS', hcS⟩ := bulkFullSupport_root_cuts value i childBound pivotBound (T false)
    (hT false) L R X lo hi d r e (hsize false) (hregular false) hL hR
  obtain ⟨U', hU', hcU⟩ := bulkFullSupport_root_cuts value i childBound pivotBound (T true)
    (hT true) L R X lo hi d r e (hsize true) (hregular true) hL hR
  let E := bulkLogCutoffFactors value i cb Dlog hDlog hloglip slots
  obtain ⟨Eroots, hEroots, hrE⟩ := bulkLogCutoffFactors_roots value i cb Dlog hDlog hloglip slots rlog hslots
  let V' := ((S ∪ U) ∪ (S' ∪ U')) ∪ Eroots
  have hcard : V'.card + 1 ≤ 2 * (A + B') + t * rlog + 1 := by
    simp only [MovingSlotData.bulkNodePolynomials_length] at hS hU
    have hsu := Finset.card_union_le S U
    have hsu' := Finset.card_union_le S' U'
    have hall := Finset.card_union_le (S ∪ U) (S' ∪ U')
    have hextra := Finset.card_union_le ((S ∪ U) ∪ (S' ∪ U')) Eroots
    dsimp only [A, B', V']
    omega
  let w := fun z => realValueSupportFlag (Function.update value i z) childBound pivotBound
    (T false) X lo hi (L.eval z) (R.eval z) *
      conj (realValueSupportFlag (Function.update value i z) childBound pivotBound
        (T true) X lo hi (L.eval z) (R.eval z))
  have hw (z : ℝ) : ‖w z‖ ≤ 1 := by
    rw [show w z = _ * conj _ from rfl, norm_mul, Complex.norm_conj]
    exact (mul_le_mul (realValueSupportFlag_norm _ _ _ _ _ _ _ _ _)
      (realValueSupportFlag_norm _ _ _ _ _ _ _ _ _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hconst (x y : ℝ) (hxy : rootCellCode V' x = rootCellCode V' y) : w x = w y := by
    have hsxy := rootCellCode_eq_of_subset S' V'
      (Finset.subset_union_left.trans (Finset.subset_union_right.trans Finset.subset_union_left)) x y hxy
    have huxy := rootCellCode_eq_of_subset U' V'
      (Finset.subset_union_right.trans (Finset.subset_union_right.trans Finset.subset_union_left)) x y hxy
    change _ * conj _ = _ * conj _
    rw [hcS x y hsxy, hcU x y huxy]
  have hroots (j) (z) (hz : z ∈ ((Fin.append
      (pairedPolynomialFactors (F false) (F true)) E) j).polynomial.derivative.roots) : z ∈ V' := by
    revert hz
    refine Fin.addCases ?_ ?_ j
    · intro j hj
      simp only [Fin.append_left] at hj
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (pairedPolynomialFactors_roots (F false) (F true) S U hrS hrU j z hj))
    · intro j hj
      simp only [Fin.append_right] at hj
      exact Finset.mem_union_right _ (hrE j z hj)
  have hbudget0 : smoothPolynomialBudget (pairedPolynomialFactors (F false) (F true)) ≤ W ^ 2 := by
    rw [pairedPolynomialFactors_budget, pow_two]
    have h0 := bulkSmoothFactors_budget value i (T false) L R ψ X lo hi V hlo hhi
      (hV false) φ G B D hB hD hφ hlip
    have h1 := bulkSmoothFactors_budget value i (T true) L R ψ X lo hi V hlo hhi
      (hV true) φ G B D hB hD hφ hlip
    exact mul_le_mul h0 h1 (smoothPolynomialBudget_nonneg _) ((smoothPolynomialBudget_nonneg _).trans h0)
  have hbudget : smoothPolynomialBudget (Fin.append
      (pairedPolynomialFactors (F false) (F true)) E) ≤
      W ^ 2 * (2 + Dlog * (Real.exp 2 - 1)) ^ t := by
    have happ : smoothPolynomialBudget (Fin.append
        (pairedPolynomialFactors (F false) (F true)) E) =
        smoothPolynomialBudget (pairedPolynomialFactors (F false) (F true)) *
          smoothPolynomialBudget E := by
      unfold smoothPolynomialBudget
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    have hE : smoothPolynomialBudget E = (2 + Dlog * (Real.exp 2 - 1)) ^ t :=
      bulkLogCutoffFactors_budget value i cb Dlog hDlog hloglip slots
    rw [happ, ← hE]
    exact mul_le_mul_of_nonneg_right hbudget0 (smoothPolynomialBudget_nonneg E)
  have he (z : ℝ) : w z * smoothPolynomialWeight (Fin.append (pairedPolynomialFactors (F false) (F true)) E) z =
      ((∏ j, bulkLogCutoffWeight (Function.update value i z) cb (slots j) : ℝ) : ℂ) *
      realValueKernelPair (Function.update value i z) childBound pivotBound T
        ψ X lo hi hlo hhi φ G (L.eval z) (R.eval z) := by
    have happ : smoothPolynomialWeight (Fin.append (pairedPolynomialFactors (F false) (F true)) E) z =
        smoothPolynomialWeight (pairedPolynomialFactors (F false) (F true)) z * smoothPolynomialWeight E z := by
      simp only [smoothPolynomialWeight, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
    rw [happ, pairedPolynomialFactors_weight,
      show smoothPolynomialWeight E z = _ from bulkLogCutoffFactors_weight value i cb Dlog hDlog hloglip slots z]
    simp only [F, bulkSmoothFactors_value value i (T false) (hT false) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout z,
      bulkSmoothFactors_value value i (T true) (hT true) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout z]
    simp only [w, realValueKernelPair, realValueKernel, map_mul]
    ring
  have h := P.gated_smooth_prime_all_roots hQ hq hqQ ha u v hu huv hshort
    (Fin.append (pairedPolynomialFactors (F false) (F true)) E) V' hroots w 1 (by norm_num) hw hconst
  simp only [he, one_mul] at h
  apply h.trans
  change (V'.card + 1 : ℕ) * smoothPolynomialBudget (Fin.append (pairedPolynomialFactors (F false) (F true)) E) *
      bulkPrimeErrorFactor P Q u ≤ ((2 * (A + B') + t * rlog + 1 : ℕ) : ℝ) *
        (W ^ 2 * (2 + Dlog * (Real.exp 2 - 1)) ^ t) * bulkPrimeErrorFactor P Q u
  apply mul_le_mul_of_nonneg_right _ (by
    dsimp only [bulkPrimeErrorFactor]
    have := P.errorConstant_nonneg
    positivity)
  exact mul_le_mul (by exact_mod_cast hcard) hbudget (smoothPolynomialBudget_nonneg _) (by positivity)

end Ostmann

end OAI
