import OAI.NumberTheory.TwoPoint.Bounds.ActualRareDeletion
import OAI.NumberTheory.TwoPoint.Bounds.ActualProhibitedDensity

namespace OAI

/-! Canonical prohibited-site deletion with all prime-family, circuit,
and rare-event hypotheses supplied by the actual bands and bin family. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def canonicalPairPadding (Q : Finset ℕ) (M : ℕ)
    (eligible : ℕ → ℕ → Prop) (d : ℕ) : Finset ℕ :=
  (boundedPaddingDivisors Q M).filter (eligible d)

theorem ModFiveThetaInput.eventually_canonical_rare_deletion
    (hP : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h : ℕ) (E : Finset ℕ) (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (eligible : ℕ → ℕ → Prop),
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let M := ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL (by linarith) hE
      let padding := canonicalPairPadding Q M eligible
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.exp (C * Real.log L) →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        prohibitedPositiveRow data ⌊L ^ (1 / 10 : ℝ)⌋₊ (primeTupleDivisors P) padding
          ((a + x.val : ℤ) + site)) ≤
        Real.exp (-L ^ (9 / 10 : ℝ)) + T * Real.exp (101 * L) * Real.exp (-(L ^ 9)) := by
  have hWone : 1 ≤ W := by linarith
  obtain ⟨A, hA, hb⟩ := hBr.eventually_actual_prohibited_deletion hP E W C hW hC
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, hP.eventually_actual_prohibited_density h E hE W hWone,
    hP.eventually_actual_pool_masses E W hWone, eventually_ge_atTop (4800 : ℝ)]
      with L hb hd hm hlarge
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let M := ⌊100 * Real.log L⌋₊
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let data := canonicalTraceFamily h E W L eligible hL hWone hE
  let padding := canonicalPairPadding Q M eligible
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hWone hE
  have hpool : (data.P ∪ data.Q).Nonempty := by
    by_contra hn
    have hempty : data.P = ∅ := not_nonempty_iff_eq_empty.mp
      (fun hp => hn (hp.mono subset_union_left))
    have hp := hm.2.2.1
    change 1 ≤ primeHarmonicMass data.P at hp
    rw [hempty] at hp
    norm_num [primeHarmonicMass] at hp
  have hJM : ((J + M : ℕ) : ℝ) ≤ L ^ 2 :=
    (prime_trace_degree_budget W L hWone hL).1.trans (by
      have hlog : Real.log L ≤ L :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      nlinarith)
  have hJ : (J : ℝ) ≤ L ^ 2 := by
    have hjle : (J : ℝ) ≤ ((J + M : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right J M
    exact hjle.trans hJM
  have hs : (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) ≤ L := by
    apply (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hL) _)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hL (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have hpair : (data.pairs.card : ℝ) ≤ Real.exp (101 * L) :=
    actualProhibitedPrimeFamily_pairs_card h J M E (L ^ (199 / 200 : ℝ)) W L η eligible
      (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hWone) hE hL hη hηone he
  have hpadding (d : ℕ) (_hd : d ∈ primeTupleDivisors P) :
      padding d ⊆ retainedPrimeDivisors data.Q := by
    intro q hq
    exact (mem_filter.mp (mem_filter.mp hq).1).1
  have hqdegree (d : ℕ) (_hd : d ∈ primeTupleDivisors P) (q : ℕ) (hq : q ∈ padding d) :
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L := by
    have hM : q.primeFactors.card ≤ M := (mem_filter.mp (mem_filter.mp hq).1).2
    have hMr : (q.primeFactors.card : ℝ) ≤ M := by exact_mod_cast hM
    exact hMr.trans (prime_trace_degree_budget W L hWone hL).2
  have hpairs (d : ℕ) (hd : d ∈ primeTupleDivisors P) (q : ℕ) (hq : q ∈ padding d) :
      (d, q) ∈ data.pairs := by
    have hm := mem_filter.mp hq
    have hq' := mem_filter.mp hm.1
    exact (actualProhibitedPrimeFamily_pairs h J M E (L ^ (199 / 200 : ℝ)) W L eligible
      (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hWone) hE d q).mpr
      ⟨hd, hq'.1, hq'.2, hm.2⟩
  intro T hT hTcap site a N hN
  have ht := hb h M ⌊Real.exp L⌋₊ ⌊L ^ (1 / 10 : ℝ)⌋₊ (J + M) data rfl rfl hB
    hpool (Nat.floor_le (Real.exp_pos _).le) hs hJM hpair data.whole_factor_card_le
    (hd hL eligible) hJ (primeTupleDivisors P) subset_rfl padding hpadding hqdegree hpairs
    T hT hTcap site a N hN
  apply ht.trans
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpair hT)
    (Real.exp_pos (-(L ^ 9))).le
  linarith

end TwoPointCorrelations

end OAI
