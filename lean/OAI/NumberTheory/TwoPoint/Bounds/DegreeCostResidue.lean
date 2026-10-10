import OAI.NumberTheory.TwoPoint.Bounds.DegreeCostComparison
import OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueEvent
import OAI.NumberTheory.TwoPoint.Bounds.PrimePaddingDeletion

namespace OAI

/-! The model degree cost preserves one reciprocal for the fixed
padding divisor. This is the estimate transferred to integer intervals. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

lemma padding_divisor_probability_le (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (q : ℕ) (hq : q ∈ retainedPrimeDivisors data.Q) (site : ℤ) :
    (data.paddingResidueLaw B hB).average (fun z =>
      if (q : ℤ) ∣ data.paddingResidueOrigin z + site then (1 : ℝ) else 0) ≤
        1 / (q : ℝ) := by
  have hsupport := retainedPrimeDivisor_factors data.Q data.primeQ hq
  have hsq := retainedPrimeDivisor_squarefree data.Q data.primeQ hq
  have he (z : data.Q → Fin B) :
      (q : ℤ) ∣ data.paddingResidueOrigin z + site ↔
        PaddingResidueEvent data.Q (fun _ : Fin 1 => q) (fun _ => site) z := by
    rw [← padding_literal_support_iff_dvd data.Q data.primeQ
      (data.paddingResidueOrigin z + site) q hq, paddingAvailablePrimes_integer]
    constructor
    · intro hz i p hp
      have hdiv := (mem_filter.mp (hz hp)).2
      exact (residue_offset_divisibility
        ((z p).val : ZMod p.val) (data.paddingResidueOrigin z) site
        (data.paddingResidueOrigin_spec z p)).mp hdiv
    · intro hz p hp
      refine mem_filter.mpr ⟨hsupport hp, ?_⟩
      let p' : data.Q := ⟨p, hsupport hp⟩
      exact (residue_offset_divisibility ((z p').val : ZMod p)
        (data.paddingResidueOrigin z) site (data.paddingResidueOrigin_spec z p')).mpr
          (hz 0 p' hp)
  have hs : paddingPrimeSupport (fun _ : Fin 1 => q) = q.primeFactors := by
    ext p
    simp only [paddingPrimeSupport, mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨0, hp⟩⟩
  have hsup : paddingPrimeSupport (fun _ : Fin 1 => q) ⊆ data.Q := by
    simpa only [hs] using hsupport
  have hh := paddingResidueEvent_probability_le data.Q (fun _ : Fin 1 => q)
    (fun _ => site) B (fun p hp => (data.primeQ p hp).pos)
    (fun p hp => hB p (mem_union_right _ hp)) hsup
  have hprod : (∏ p ∈ paddingPrimeSupport (fun _ : Fin 1 => q), (p : ℝ)⁻¹) =
      1 / (q : ℝ) := by
    rw [hs]
    rw [prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq, one_div]
  rw [hprod] at hh
  simpa [FiniteLaw.probability, he, ProhibitedPrimeFamily.paddingResidueLaw] using hh

theorem positive_divisor_degree_cost (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (q : ℕ) (hq : q ∈ retainedPrimeDivisors data.Q)
    (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight S (data.residueOrigin x + site) *
        if (q : ℤ) ∣ data.residueOrigin x + site ∧
          6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) ≤
      actualPaddingCoefficient q / q * positivePrimeNormalizer S *
        Real.exp (-2 * W * S.card) := by
  let g := fun n : ℤ => if (q : ℤ) ∣ n then (1 : ℝ) else 0
  have hg0 (n) : 0 ≤ g n := by dsimp [g]; split_ifs <;> norm_num
  have hg (n m : ℤ) (he : ∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) : g n = g m := by
    have hd := squarefree_divisor_congr data.Q q
      (retainedPrimeDivisor_squarefree data.Q data.primeQ hq)
      (retainedPrimeDivisor_factors data.Q data.primeQ hq) n m he
    simp only [g, hd]
  have hh := data.positive_prime_padding_degree_tail hB S hSP W hW hmass site g hg0 hg
  have hprob := data.padding_divisor_probability_le hB q hq site
  have hconstant : 0 ≤ positivePrimeNormalizer S * Real.exp (-2 * W * S.card) := by
    unfold positivePrimeNormalizer
    positivity
  have hbound := hh.trans (mul_le_mul_of_nonneg_left hprob hconstant)
  have hm := mul_le_mul_of_nonneg_left hbound (actualPaddingCoefficient_nonneg q)
  calc
    _ = actualPaddingCoefficient q * (data.residueLaw B hB).average (fun x =>
        (positivePrimeWeight S (data.residueOrigin x + site) *
          if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
            then 1 else 0) * g (data.residueOrigin x + site)) := by
      rw [mul_comm (actualPaddingCoefficient q) _, ← FiniteLaw.average_mul_const]
      apply congrArg (data.residueLaw B hB).average
      funext x
      dsimp [g]
      split_ifs <;> simp_all
      all_goals ring
    _ ≤ _ := by convert hm using 1; ring

end ProhibitedPrimeFamily

theorem BravermanDepth22Input.eventually_integer_degree_cost
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (W : ℝ), 10 ≤ W → 6 * W * S.card ≤ 400 * Real.log L →
      (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N =>
        actualPaddingCoefficient q * positivePrimeWeight S ((a + x.val : ℤ) + site) *
          if (q : ℤ) ∣ (a + x.val : ℤ) + site ∧
            6 * W * S.card < (actualPaddingDegree data.P ((a + x.val : ℤ) + site) : ℝ)
            then 1 else 0) ≤
        actualPaddingCoefficient q / q * positivePrimeNormalizer S *
          Real.exp (-2 * W * S.card) + Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_degree_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL S hSP hSL W hW hTL hmass q hq hqdegree site a N hN
  have hc := hb h J M B data hB hpool hBL S data.P
    (hSP.trans subset_union_left) subset_union_left hSL q hq hqdegree
    (6 * W * S.card) (by positivity) hTL site a N hN
  have hm := data.positive_divisor_degree_cost hB S hSP q hq W hW hmass site
  dsimp only at hc
  have hu := le_trans (le_abs_self _) hc
  linarith

end TwoPointCorrelations

end OAI
