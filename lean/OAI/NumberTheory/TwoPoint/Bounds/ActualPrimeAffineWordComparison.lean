import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeWordComparison

namespace OAI

/-! Canonical prime bands exclude every prime factor of the progression
modulus, so the affine-origin word comparison has no additional premise. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma canonicalTraceFamily_coprime (h l : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) :
    ∀ p ∈ (canonicalTraceFamily h E W L eligible hL hW hE).P ∪
      (canonicalTraceFamily h E W L eligible hL hW hE).Q, l.Coprime p := by
  intro p hp
  have hprime := (canonicalTraceFamily h E W L eligible hL hW hE).prime ⟨p, hp⟩
  have hnot : p ∉ E := by
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
      exact (centeredPrimeSupply_mem hj).2.2.1
    · exact (mem_sdiff.mp hp).2
  exact (hprime.coprime_iff_not_dvd.mpr (fun hd => hnot (hEl p hprime hd))).symm

theorem ModFiveThetaInput.eventually_actual_prime_affine_word_comparison_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (E : Finset ℕ) (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E)
    (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ (w : ColumnPrimeAssignment J (2 * ⌊L⌋₊) P) (forward : Fin (2 * ⌊L⌋₊) → Bool)
        (padding : Fin (2 * ⌊L⌋₊) → Q),
      wordDisplacement h (columnTupleWord w forward (fun i => (padding i).val)) = 0 →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N => scalarWalkProduct h weight (a + l * x.val)
          (columnTupleWord w forward (fun i => (padding i).val))) -
        (data.residueLaw B hB).average (fun r => scalarWalkProduct h weight (data.residueOrigin r)
          (columnTupleWord w forward (fun i => (padding i).val)))| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hcompare⟩ := hBr.eventually_actual_affine_word_comparison
  refine ⟨A, hA, ?_⟩
  intro h l E hE hEl W hW
  filter_upwards [hcompare, hprime.eventually_actual_pool_masses E W hW,
    eventually_ge_atTop (4800 : ℝ)] with L hcompare hmasses hlarge
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
  have hpool : (data.P ∪ data.Q).Nonempty := by
    by_contra hn
    have hempty : data.P = ∅ := not_nonempty_iff_eq_empty.mp
      (fun hp => hn (hp.mono subset_union_left))
    have hp := hmasses.2.2.1
    change 1 ≤ primeHarmonicMass data.P at hp
    rw [hempty] at hp
    norm_num [primeHarmonicMass] at hp
  have hdegree := prime_trace_degree_budget W L hW hL
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hJM : ((J + ⌊100 * Real.log L⌋₊ : ℕ) : ℝ) ≤ L ^ 2 :=
    hdegree.1.trans (by nlinarith)
  have hs : (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) ≤ L := by
    apply (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hL (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have hk : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hkpos : 0 < ⌊L⌋₊ := by
    apply (Nat.le_floor_iff (by linarith : 0 ≤ L)).mpr
    simpa using hL
  have hRL : ((2 * ⌊L⌋₊ + 1 : ℕ) : ℝ) ≤ 4 * L := by push_cast; linarith
  have hJ : (J : ℝ) ≤ L / 2 := by
    have hc := primeSupplyCount_mul_bound W L (by linarith) hL
    change (J : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L at hc
    have hj : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hRJ : ((2 * ⌊L⌋₊ * J : ℕ) : ℝ) ≤ L ^ 2 := by
    push_cast
    nlinarith [mul_le_mul hk hJ (Nat.cast_nonneg J) (by linarith : 0 ≤ L)]
  have hpair : (data.pairs.card : ℝ) ≤ Real.exp (101 * L) :=
    actualProhibitedPrimeFamily_pairs_card h J ⌊100 * Real.log L⌋₊ E
      (L ^ (199 / 200 : ℝ)) W L η eligible (Real.rpow_nonneg (by linarith) _)
      (by linarith) hE hL hη hηone he
  intro w forward padding hclosed a N hN
  have hq : Q ⊆ retainedPrimeDivisors data.Q := fun q hq => (mem_filter.mp hq).1
  exact hcompare h J ⌊100 * Real.log L⌋₊ (2 * ⌊L⌋₊) ⌊L ^ (1 / 10 : ℝ)⌋₊
    ⌊Real.exp L⌋₊ data hB hpool (Nat.floor_le (Real.exp_pos _).le) hs hJM hpair
    (by omega) hRL hRJ Q hq P w forward (fun i => (padding i).val)
    (centeredPrimeBands_prime E _ W J)
    (centeredPrimeBands_disjoint E _ W J (Real.rpow_nonneg (by linarith) _) (by linarith))
    (fun i => (show (((padding i).val.primeFactors.card : ℕ) : ℝ) ≤
      (⌊100 * Real.log L⌋₊ : ℝ) by exact_mod_cast (mem_filter.mp (padding i).property).2).trans hdegree.2)
    (actualColumnLabel data (fun j => centeredPrimeBand_subset_pool E _ W J j) w)
    (fun _ _ => rfl) hclosed (fun d q => (d, q) ∈ data.pairs) (Real.exp (4 * J)) a l N
    (canonicalTraceFamily_coprime h l E W L eligible hL hW hE hEl) hN

theorem ModFiveThetaInput.eventually_actual_prime_affine_word_comparison
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h l : ℕ) (E : Finset ℕ) (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E)
    (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ (w : ColumnPrimeAssignment J (2 * ⌊L⌋₊) P) (forward : Fin (2 * ⌊L⌋₊) → Bool)
        (padding : Fin (2 * ⌊L⌋₊) → Q),
      wordDisplacement h (columnTupleWord w forward (fun i => (padding i).val)) = 0 →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N => scalarWalkProduct h weight (a + l * x.val)
          (columnTupleWord w forward (fun i => (padding i).val))) -
        (data.residueLaw B hB).average (fun r => scalarWalkProduct h weight (data.residueOrigin r)
          (columnTupleWord w forward (fun i => (padding i).val)))| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hbound⟩ := hprime.eventually_actual_prime_affine_word_comparison_uniform hBr
  exact ⟨A, hA, hbound h l E hE hEl W hW⟩

end TwoPointCorrelations

end OAI
