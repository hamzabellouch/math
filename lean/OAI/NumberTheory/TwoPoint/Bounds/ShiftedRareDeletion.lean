import OAI.NumberTheory.TwoPoint.Bounds.ShiftedRareComparison
import OAI.NumberTheory.TwoPoint.Walks.CanonicalRareDeletion

namespace OAI

/-! The actual rare-event deletion bound is unchanged by separate endpoint
shifts for each pair. All arithmetic and circuit budgets are supplied here. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion_uniform
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (E : Finset ℕ) (W C : ℝ),
      10 ≤ W → 0 ≤ C → ∀ᶠ L : ℝ in atTop,
      ∀ (h M B s cap : ℕ) (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      (data.residueLaw B hB).probability (data.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      (primeSupplyCount W L : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors
        (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      (∀ d ∈ D, ∀ q ∈ padding d, (d, q) ∈ data.pairs) →
      ∀ (T : ℝ), 0 ≤ T → T ≤ Real.exp (C * Real.log L) →
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        shiftedProhibitedRow data s D padding site (a + x.val)) ≤
          Real.exp (-L ^ (9 / 10 : ℝ)) +
            T * data.pairs.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hc⟩ := hBr.eventually_shifted_prohibited_row_comparison
  refine ⟨A, hA, ?_⟩
  intro E W C hW hC
  filter_upwards [hc, hP.eventually_prohibited_model_row E W C hW hC,
    eventually_ge_atTop (1 : ℝ)] with L hc hm hL
  intro h M B s cap data hp hq hB hpool hBL hs hcap hpair hdegree hprob hJ D hD
    padding hpadding hqdegree hpairs T hT hTcap site a N hN
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  have hprime := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  have hdisj := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
    (Real.rpow_nonneg (by linarith) _) (by linarith : 0 ≤ W)
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hprime hdisj (hD hd)
  have hsupport (d : ℕ) (hmem : d ∈ D) : d.primeFactors ⊆ data.P ∪ data.Q := by
    apply (hd d hmem).2.2.trans
    rw [hp]
    exact subset_union_left
  have hcard (d : ℕ) (hmem : d ∈ D) : (d.primeFactors.card : ℝ) ≤ L ^ 2 := by
    rw [(hd d hmem).2.1]
    exact hJ
  have hcompare := hc h (primeSupplyCount W L) M B s cap data hB hpool hBL hs hcap
    hpair hdegree D hsupport hcard padding hpadding hqdegree site a N hN
  have hcompare' : |uniformAverage (fun x : Fin N =>
      shiftedProhibitedRow data s D padding site (a + x.val)) -
        (data.residueLaw B hB).average (fun x =>
          prohibitedPositiveRow data s D padding (data.residueOrigin x))| ≤
      (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
    simpa only [shiftedProhibitedRow, uniformAverage_finset_sum] using hcompare
  have hmodel := hm h M B s data hp hq hB hprob D hD padding hpadding T hT hTcap 0
  simp only [add_zero] at hmodel
  have hcount : ((∑ d ∈ D, (padding d).card : ℕ) : ℝ) ≤ data.pairs.card := by
    exact_mod_cast padding_pair_count_le D padding data.pairs hpairs
  have hdiff := (le_abs_self _).trans hcompare'
  have hdiffT := mul_le_mul_of_nonneg_left hdiff hT
  have hcountT := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcount (Real.exp_pos (-(L ^ 9))).le) hT
  nlinarith


theorem BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h M B s cap : ℕ) (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      (data.residueLaw B hB).probability (data.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      (primeSupplyCount W L : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors
        (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      (∀ d ∈ D, ∀ q ∈ padding d, (d, q) ∈ data.pairs) →
      ∀ (T : ℝ), 0 ≤ T → T ≤ Real.exp (C * Real.log L) →
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        shiftedProhibitedRow data s D padding site (a + x.val)) ≤
          Real.exp (-L ^ (9 / 10 : ℝ)) +
            T * data.pairs.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_shifted_actual_prohibited_deletion_uniform hP
  exact ⟨A, hA, hb E W C hW hC⟩

theorem ModFiveThetaInput.eventually_shifted_canonical_rare_deletion_uniform
    (hP : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (h : ℕ) (E : Finset ℕ)
      (hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∀ (W C : ℝ) (hW : 10 ≤ W) (_hC : 0 ≤ C), ∀ᶠ L : ℝ in atTop,
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
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        shiftedProhibitedRow data ⌊L ^ (1 / 10 : ℝ)⌋₊ (primeTupleDivisors P) padding
          site (a + x.val)) ≤
        Real.exp (-L ^ (9 / 10 : ℝ)) + T * Real.exp (101 * L) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_shifted_actual_prohibited_deletion_uniform hP
  refine ⟨A, hA, ?_⟩
  intro h E hE W C hW hC
  have hWone : 1 ≤ W := by linarith
  have hb := hb E W C hW hC
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


theorem ModFiveThetaInput.eventually_shifted_canonical_rare_deletion
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
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        shiftedProhibitedRow data ⌊L ^ (1 / 10 : ℝ)⌋₊ (primeTupleDivisors P) padding
          site (a + x.val)) ≤
        Real.exp (-L ^ (9 / 10 : ℝ)) + T * Real.exp (101 * L) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hP.eventually_shifted_canonical_rare_deletion_uniform hBr
  exact ⟨A, hA, hb h E hE W C hW hC⟩

end TwoPointCorrelations

end OAI
