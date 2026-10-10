import OAI.NumberTheory.Ostmann.Characters.SparseTailSieveContradiction
import OAI.NumberTheory.Ostmann.Characters.SparseTailCoverage
import OAI.NumberTheory.Ostmann.Preliminaries.SqrtSieveGeometry
import OAI.NumberTheory.Ostmann.Characters.SparseSubsetParameters

namespace OAI

/-! # Sparse balanced tail spectra have small harmonic mass

This is the contradiction step of Proposition 5.1, using the original
nonnegative sparse weight and the actual positive and reflected summand tails.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.sparse_tail_mass_bound
    (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM : ℝ) (hM : MertensEstimate CM)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) :
    ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
      ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
        ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
        ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)],
          Pairwise (fun i j => (p i).Coprime (p j)) →
          (∀ i, p i ∈ logLogPrimeBand L) →
          (∀ i, (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i))) →
          (∀ i, residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3) →
          ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 1000000 →
          (∀ i, (p i : ℝ)⁻¹ * ∑ b,
            ‖normalizedResidueTransform (tailDensityMask A N (p i)) b‖ ≤ ε ^ 2) →
          (∑ i, (p i : ℝ)⁻¹) ≤ L →
          (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
          (∑ i, (p i : ℝ)⁻¹) < (17 / 25 : ℝ) * L := by
  obtain ⟨N, hN, hsieve⟩ := h.sqrt_scale_sieve_log_budget_with_disjoint hsize hA hB CM hM
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  refine ⟨N, hN, ?_⟩
  filter_upwards [hsieve, eventual_sqrt_sieve_geometry N,
    eventual_sparse_subset_parameters 2002 (by norm_num),
    Real.tendsto_exp_atTop.eventually hlarge,
    h.sparse_tail_coverage hsize hA hB Z hD hR P hPNT 1000 (by norm_num),
    eventual_sparse_coverage_margin ((∫ t : ℝ, primeMeanTest t) / 8)
      (div_pos primeMeanTest_integral_pos (by norm_num)),
    eventually_ge_atTop (10000 : ℝ)] with L hsieve hgeom hsub hlarge hcoverage hmargin hL
  obtain ⟨exception, he⟩ := hcoverage
  refine ⟨exception, ?_⟩
  intro X hX n p hp hnprod hc hpband hlo hhi ε hε hεsmall hL1 hH havoid
  by_contra hmass
  have hmass' : (17 / 25 : ℝ) * L ≤ ∑ i, (p i : ℝ)⁻¹ := le_of_not_gt hmass
  have hp100 (i : Fin n) : (100 : ℝ) ≤ p i := by
    have hh := (logLogPrimeBand_mem (hpband i)).2.1
    have he := Real.add_one_le_exp ((1 / 20 : ℝ) * L)
    have hl := Real.log_le_self (Nat.cast_nonneg (p i))
    linarith
  have hSp (i : Fin n) : (tailDensityMask A N (p i)).card < p i :=
    tailDensityMask_card_lt hB N _ (Fact.out : (p i).Prime).pos (hN _ Fact.out)
  have hS (i : Fin n) : (tailDensityMask A N (p i)).Nonempty :=
    tailDensityMask_nonempty hA N _ (Fact.out : (p i).Prime).pos
  obtain ⟨_, hcov⟩ := he X hX n p (fun i => tailDensityMask A N (p i)) hc hS hSp
    hp100 hlo hhi ε hε hεsmall hL1 hH
    (fun i => (logLogPrimeBand_mem (hpband i)).2.2) havoid
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge X hX
  have hpositive : 0 < a * Real.exp (Real.exp L / 2) / Real.exp L ^ 3 := by positivity
  have hAt : (positiveSummandTail A (summandTailCutoff (Real.exp L)) X).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast lt_of_lt_of_le hpositive hsa)
  have hBt : (negativeSummandTail B (summandTailCutoff (Real.exp L)) X).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast lt_of_lt_of_le hpositive hsb)
  let K := sparseTruncationDegree 1000 L
  have hK : 1000 * L ≤ (K : ℝ) := Nat.le_ceil _
  have hKu : (K : ℝ) ≤ 1000 * L + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (1000 : ℝ) * L)).le
  have hsub' (T : Finset (Fin n)) (hT : T.card ≤ 2 * K) :
      (∏ i ∈ T, p i) ≤ ⌊Real.exp (Real.exp L / 2)⌋₊ ∧
      (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16 := by
    apply hsub n p hpband T
    have ht : (T.card : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hT
    linarith
  apply sparse_tail_sieve_contradiction ls hA hB N (summandTailCutoff (Real.exp L)) X
    ⌊Real.exp (Real.exp L / 2)⌋₊ hN hgeom.2.2.2 hgeom.1 hAt hBt p hc
    (fun i => Nat.le_of_mem_primesLE
      (logLogPrimeBand_subset_sqrt_cutoff L (by linarith) (hpband i)))
    hp100 hlo hhi ε hε hεsmall hL1 L (by linarith) hH hmass' K hK
    (fun T hT => (hsub' T hT).1) (fun T hT => (hsub' T hT).2)
    (hsieve X hX _ (Finset.Subset.refl _)) ((∫ t : ℝ, primeMeanTest t) / 8)
    (div_pos primeMeanTest_integral_pos (by norm_num)) hcov
    (by rw [hX, Real.log_exp]) (by rw [hX]; positivity)
    (by simpa only [hX] using hgeom.2.1)
    (by simpa only [hX] using hgeom.2.2.1) hmargin

end Ostmann

end OAI
