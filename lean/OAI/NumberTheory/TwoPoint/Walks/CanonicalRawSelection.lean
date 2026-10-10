import OAI.NumberTheory.TwoPoint.Bounds.RawPairSelection
import OAI.NumberTheory.TwoPoint.Bounds.PrimeCostTails
import OAI.NumberTheory.TwoPoint.Walks.CanonicalRetainedMass

namespace OAI

/-! Finite prime-defect tails supply the required numerical phase selection
for the canonical graph at every sufficiently large auxiliary scale. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem canonical_raw_pair_selection (hP : ModFiveThetaInput) {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (hsf : Summable (fun p : ℕ => if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0))
    (hsg : Summable (fun p : ℕ => if p.Prime then (1 - ‖g p‖) / (p : ℝ) else 0))
    (h : ℕ) (hh : 0 < h) (W γ : ℝ) (hW : 1 ≤ W) (hγ : 0 < γ) :
    ∃ E : Finset ℕ, (∀ p, p.Prime → p ∣ h → p ∈ E) ∧
      ∀ᶠ L : ℝ in atTop, ∀ _hL : 1 ≤ L, ∀ η : ℝ, 0 < η →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
      0 < S₀ ∧ ∃ A ⊆ eligibleComplexPairs (primeTupleDivisors P) Q (PaddingPairEligible L η),
        S₀ / 8 ≤ ‖selectedRawCoefficient A f g‖ ∧
        (∑ dq ∈ A, complexPairWeight dq) ≤ S₀ ∧
        (∑ dq ∈ A, complexPairWeight dq *
          ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤ γ * S₀ / 128 := by
  let ε := min (1 / 100 : ℝ) (γ / 1280)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨E, hE, htail⟩ := exists_prime_defect_exclusion hf hg hsf hsg h.primeFactors ε hε
  refine ⟨E, fun p hp hph => hE (Nat.mem_primeFactors.mpr ⟨hp, hph, hh.ne'⟩), ?_⟩
  filter_upwards [hP.eventually_actual_prime_supplies E W hW,
    hP.eventually_canonical_retained_mass E W hW] with L hs hm
  intro hL η hη
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  have hp : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ j k, k ≠ j → Disjoint (P j) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
  have hq : ∀ p ∈ Q, p.Prime := fun _ hq => paddingPrimeSupply_prime hq
  have hPQ : Disjoint (primeTuplePool P) Q := centeredPrimePool_disjoint_padding _ _ _ _ _
  have hpE : Disjoint (primeTuplePool P) E := by
    apply disjoint_left.mpr
    intro p hp hpe
    obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
    exact (centeredPrimeSupply_mem hj).2.2.1 hpe
  have hqE : Disjoint Q E := by
    apply disjoint_left.mpr
    intro p hp hpe
    exact (mem_sdiff.mp hp).2 hpe
  have htp := htail (primeTuplePool P) (fun _ hp' => primeTuplePool_prime hp hp') hpE
  have htq := htail Q hq hqE
  have hmass : ∀ j, W ≤ primeHarmonicMass (P j) := by
    intro j
    simpa only [primeHarmonicMass_eq_sum, P, centeredPrimeBands] using (hs.2.2 j.val).2.1
  have htotal := (hm hL η hη).2
  have hV : 1 ≤ ∏ j, primeHarmonicMass (P j) :=
    one_le_prod₀ (fun j _ => hW.trans (hmass j))
  have hS₀ : 0 < totalPaddingBinMass (primeTupleDivisors P) Q L η :=
    (half_pos (mul_pos (paddingTiltNormalizer_pos Q) (lt_of_lt_of_le zero_lt_one hV))).trans_le htotal
  refine ⟨hS₀, ?_⟩
  exact select_raw_pair_family hfm hgm hf1 hg1 hf hg P Q hp hd hq hPQ W L η γ
    hW hη hγ.le hmass htotal
    (htp.1.le.trans (min_le_left _ _)) (htq.1.le.trans (min_le_left _ _))
    (htp.2.le.trans (min_le_right _ _)) (htq.2.le.trans (min_le_right _ _))

end TwoPointCorrelations

end OAI
