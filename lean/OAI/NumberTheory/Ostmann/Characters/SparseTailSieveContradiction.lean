import OAI.NumberTheory.Ostmann.Supply.EnumeratedTailSieveEnergy
import OAI.NumberTheory.Ostmann.Supply.TailSparsePairSum
import OAI.NumberTheory.Ostmann.Characters.SparseNumericalContradiction

namespace OAI

/-! # The concrete sparse contradiction on the original summand tails -/
namespace Ostmann
open scoped Classical BigOperators

theorem sparse_tail_sieve_contradiction (ls : PublishedAdditiveLargeSieve)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (N lo X Q : ℕ)
    (hdis : ∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q))
    (hcut : N + Q ≤ lo) (hQ : 1 ≤ Q)
    (hAt : (positiveSummandTail A lo X).Nonempty)
    (hBt : (negativeSummandTail B lo X).Nonempty)
    {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (hpQ : ∀ i, p i ≤ Q)
    (hp100 : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i)))
    (hhi : ∀ i, residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b,
      ‖normalizedResidueTransform (tailDensityMask A N (p i)) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (hHlow : (17 / 25) * L ≤ ∑ i, (p i : ℝ)⁻¹)
    (K : ℕ) (hK : 1000 * L ≤ K)
    (hprod : ∀ T : Finset (Fin n), T.card ≤ 2 * K → (∏ i ∈ T, p i) ≤ Q)
    (hsmall : ∀ T : Finset (Fin n), T.card ≤ 2 * K →
      (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ q ∈ Nat.primesLE Q,
      |Real.log (((Finset.range q \ tailSupport A N q).card : ℝ) /
        (tailSupport A N q).card)| / q) ≤ L ^ (3 / 4 : ℝ) / 16)
    (c : ℝ) (hcpos : 0 < c)
    (hcover : c * (∏ i, sparseKernelUnitFactor (p i)
        (((largeTransformSpectrum (normalizedResidueTransform (tailDensityMask A N (p i)))).card : ℝ) / p i)) * X ≤
      Real.log X * ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X,
        sparseSubsetWeight p (fun i => tailDensityMask A N (p i)) K
          (fun i => ((a + b : ℕ) : ZMod (p i))))
    (hlogX : Real.log (X : ℝ) = Real.exp L) (hX : 0 < (X : ℝ))
    (hQsize : (X : ℝ) / 4 ≤ (Q : ℝ) ^ 2)
    (hDsize : ((X : ℝ) + 1) + (Q : ℝ) ^ 2 ≤ 3 * X)
    (hmargin : 18432 * Real.exp (L - (8 / 5) * ((17 / 25) * L) +
      2 * L ^ (3 / 4 : ℝ)) < c) : False := by
  have hb := enumerated_tail_sieve_energy_budgets ls hA hB N lo X Q hdis hcut hQ
    hAt hBt p hc hpQ (2 * K) hprod hsmall (L ^ (3 / 4 : ℝ))
    (Real.rpow_pos_of_pos (by linarith) _) hP
  let S := fun i => tailDensityMask A N (p i)
  have hS (i : Fin n) : (S i).Nonempty := tailDensityMask_nonempty hA N _ (Fact.out : (p i).Prime).pos
  have hSp (i : Fin n) : (S i).card < p i :=
    tailDensityMask_card_lt hB N _ (Fact.out : (p i).Prime).pos (hdis _ Fact.out)
  have hcover' := summandTail_sparse_coverage p S K A B lo X _ (Real.exp L) hlogX hcover
  have hfinal := sparse_pair_coverage_size_bound p S hS hSp hp100 hlo hhi ε hε hεsmall hL1
    L hL hH K hK (positiveSummandTail A lo X) (negativeSummandTail B lo X) hAt hBt
    (fun x i => (x : ZMod (p i))) (fun x i => (x : ZMod (p i)))
    (fun x hx i => positiveSummandTail_mem_mask A N lo X _ (Fact.out : (p i).Prime).pos
      (by have := hpQ i; omega) hx)
    (fun x hx i => negativeSummandTail_mem_mask_complement N lo X _ (Fact.out : (p i).Prime).pos
      (hdis _ Fact.out) (by have := hpQ i; omega) hx)
    ((Q : ℝ) / 16 * Real.exp (-(L ^ (3 / 4 : ℝ))))
    (((X : ℝ) + 1) + (Q : ℝ) ^ 2) c X (Real.exp L)
    (by positivity) (by positivity) hcpos.le hX.le (Real.exp_nonneg _) ?_ ?_ hcover'
  · apply sparse_sieve_numerical_impossible c _ X Q (((X : ℝ) + 1) + (Q : ℝ) ^ 2)
      (∑ i, (p i : ℝ)⁻¹) L hcpos ?_ hX (by positivity) hQsize hDsize hHlow hmargin hfinal
    exact (sparse_finite_contraction p S hS hSp hp100 hlo hhi ε hε hεsmall hL1 L hL hH K hK).1
  · simpa only [positiveSummandTail_card, S] using hb.1
  · simpa only [negativeSummandTail_card, S] using hb.2

end Ostmann

end OAI
