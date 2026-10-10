import OAI.NumberTheory.Ostmann.Construction.ActualSmallEndpointBudget
import OAI.NumberTheory.Ostmann.Characters.SparsePrimeFamilyCard
import OAI.NumberTheory.Ostmann.Characters.SparsePrimeLowerBound

namespace OAI

/-! # Full prime coverage forces a large sparse weight on the actual tails -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.sparse_tail_coverage
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) (C : ℝ) (hC : 1000 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (S : ∀ i, Finset (ZMod (p i))),
        Pairwise (fun i j => (p i).Coprime (p j)) →
        (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
        (∀ i, (100 : ℝ) ≤ p i) →
        (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
        (∀ i, residueDensity (S i) ≤ 2 / 3) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 1000000 →
        (∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2) →
        (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        let U := ∏ i, sparseKernelUnitFactor (p i)
          (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
        0 < U ∧ ((∫ t : ℝ, primeMeanTest t) / 8) * U * X ≤
          Real.log X * ∑ a ∈ summandTail A (summandTailCutoff (Real.exp L)) X,
            ∑ b ∈ summandTail B (summandTailCutoff (Real.exp L)) X,
              sparseSubsetWeight p S (sparseTruncationDegree C L)
                (fun i => ((a + b : ℕ) : ZMod (p i))) := by
  obtain ⟨N, hcoverage⟩ := h.smooth_coverage
  have hlim : Tendsto (fun L : ℝ => Real.exp (Real.exp L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop
  filter_upwards [sparseWeightedPrimeSum_lower Z hD hR P hPNT C hC,
    h.small_endpoint_budget hsize hA hB 10,
    eventual_sparse_weight_subpower C (1 / 100) (by linarith) (by norm_num),
    eventual_sparse_prime_error_margin (∫ t : ℝ, primeMeanTest t) primeMeanTest_integral_pos,
    hlim.eventually_ge_atTop (2 * (N : ℝ)), eventually_ge_atTop (1 : ℝ)]
    with L hprime hdelete hweight hmargin hlarge hL
  obtain ⟨exception, he⟩ := hprime
  refine ⟨exception, ?_⟩
  intro X hX n p hp hprod S hc hS hSp hp100 hlo hhi ε hε hεsmall hL1 hH hlog havoid U
  obtain ⟨hU, hUlow, hprime⟩ := he n p S hc hS hSp hp100 hlo hhi ε hε hεsmall hL1 hH hlog havoid
  refine ⟨hU, ?_⟩
  let K := sparseTruncationDegree C L
  let lo := summandTailCutoff (Real.exp L)
  let W := fun q : ℕ => sparseSubsetWeight p S K (fun i => (q : ZMod (p i)))
  let M : ℝ := ((K + 1 : ℝ) * (n + 1 : ℝ) ^ K) ^ 2
  have hW (q : ℕ) : W q ≤ M := sparseSubsetWeight_uniform_bound p S K _
  have hWpos (q : ℕ) : 0 ≤ W q := sparseSubsetWeight_nonneg p S K _
  have hX1 : 1 ≤ (X : ℝ) := by rw [hX]; exact Real.one_le_exp (Real.exp_nonneg _)
  have hlog0 := Real.log_nonneg hX1
  have hcov := hcoverage X hX1 (by simpa only [hX] using hlarge) W hWpos
  have hMw : M ≤ Real.exp (Real.exp L / 100) := by
    simpa only [M, K, div_eq_mul_inv, one_mul, mul_comm] using hweight n (sparse_prime_family_card p hc L hlog)
  have hdel := hdelete X hX M (sq_nonneg _) hMw
  have hloX : lo ≤ X := by
    have he : (lo : ℝ) ≤ Real.exp (9 * Real.exp L / 10) := Nat.floor_le (Real.exp_nonneg _)
    have hle : Real.exp (9 * Real.exp L / 10) ≤ Real.exp (Real.exp L) :=
      Real.exp_le_exp.mpr (by linarith [Real.exp_pos L])
    have hh := he.trans hle
    rw [← hX] at hh
    exact_mod_cast hh
  have hsplit := mul_le_mul_of_nonneg_left
    (prefix_pair_sum_le_tail A B lo X hloX W M (sq_nonneg _) hW) hlog0
  rw [mul_add] at hsplit
  have hecost : (X : ℝ) * Real.exp (-10 * L) ≤
      ((∫ t : ℝ, primeMeanTest t) / 8) * U * X := by
    have hmar : Real.exp (-10 * L) ≤ ((∫ t : ℝ, primeMeanTest t) / 8) * U := by
      have hpos : 0 ≤ (∫ t : ℝ, primeMeanTest t) / 4 :=
        div_nonneg primeMeanTest_integral_pos.le (by norm_num)
      have hh := mul_le_mul_of_nonneg_left hUlow hpos
      linarith
    have hh := mul_le_mul_of_nonneg_right hmar (Nat.cast_nonneg X)
    nlinarith only [hh]
  have hprime' : ((∫ t : ℝ, primeMeanTest t) / 4) * U * X ≤
      ∑ q ∈ (Finset.Ioc 0 ⌊(X : ℝ)⌋₊).filter Nat.Prime,
        Real.log q * W q * primeMeanTest (q / X) := by
    simpa only [← hX, sparseWeightedPrimeSum] using hprime
  have herr : Real.log X * (M *
      (((summandPrefix A lo).card : ℝ) * (summandPrefix B X).card +
        ((summandPrefix A X).card : ℝ) * (summandPrefix B lo).card)) ≤
      ((∫ t : ℝ, primeMeanTest t) / 8) * U * X := by
    have hh : Real.log X * (M *
        (((summandPrefix A lo).card : ℝ) * (summandPrefix B X).card +
          ((summandPrefix A X).card : ℝ) * (summandPrefix B lo).card)) ≤
        (X : ℝ) * Real.exp (-10 * L) := by
      simpa only [lo, mul_assoc] using hdel
    exact hh.trans hecost
  change _ ≤ Real.log X * ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X, W (a + b)
  simp only [Nat.floor_natCast] at hcov hprime'
  linarith

end Ostmann

end OAI
