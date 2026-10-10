import OAI.NumberTheory.TwoPoint.Bounds.ActualMatrixTrace
import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingWeights
import OAI.NumberTheory.TwoPoint.Bounds.PrimeTraceParameters

namespace OAI

/-! The residue-model trace bound for the actual prime supplies and padding
normalization. Its only analytic input is the cited fixed-modulus prime theorem. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def canonicalTraceFamily (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) :
    ProhibitedPrimeFamily h (primeSupplyCount W L) ⌊100 * Real.log L⌋₊ :=
  actualProhibitedPrimeFamily h (primeSupplyCount W L) ⌊100 * Real.log L⌋₊ E
    (L ^ (199 / 200 : ℝ)) W L eligible
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW) hE

lemma canonicalTraceFamily_residue_bound (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) :
    ∀ p ∈ (canonicalTraceFamily h E W L eligible hL hW hE).P ∪
      (canonicalTraceFamily h E W L eligible hL hW hE).Q, p ≤ ⌊Real.exp L⌋₊ :=
  fun _ hp => actualProhibitedPrimeFamily_residue_bound h _ _ E _ W L eligible _ _ hE
    (primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL) hp

theorem ModFiveThetaInput.eventually_actual_prime_matrix_trace (hprime : ModFiveThetaInput)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      let g := actualPaddingVertex Qp
      let keep := fun n => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) n
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) g (fun d => centeredTuple d.primeFactors)
        L (Real.exp (4 * J)) (fun _ => actualPaddingDegreeCut Qp L) h keep
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (embed : V → ((j : Fin J) → P j) × ℤ), Function.Injective embed →
      (Fintype.card V : ℝ) ≤ Real.exp (106 * L) →
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
        (shiftMatrix embed (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
          (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
            (fun t n => weight t (n + data.residueOrigin r))) ^ ⌊L⌋₊)) ≤
        (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [eventually_actual_matrix_trace h 101 W hh (by norm_num) hW,
    hprime.eventually_actual_pool_masses E W hW] with L htrace hmasses
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
  have hA : 0 < A := Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _
  have hend : primeSupplyEndpoint A W J ≤ L :=
    primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL
  have hP (j : Fin J) : P j ⊆ data.P := centeredPrimeBand_subset_pool E A W J j
  have hdegree := prime_trace_degree_budget W L hW hL
  have hep := prime_trace_endpoints L hL
  have hq (q : ℕ) (hq : q ∈ Q) : q ∈ retainedPrimeDivisors Qp := (mem_filter.mp hq).1
  intro V _ _ embed hinj hdim gate
  apply htrace J ⌊100 * Real.log L⌋₊ ⌊Real.exp L⌋₊ ⌈Real.exp A⌉₊
    ⌊Real.exp L⌋₊ ⌊Real.exp (100 * L + 1)⌋₊ ⌊Real.exp (2 * L)⌋₊ data hB P Q hP
    hmasses.1 hdegree.1
    (fun j => (hmasses.2.1 j).1) (fun j => (hmasses.2.1 j).2.1)
    (fun j => (hmasses.2.1 j).2.2)
    hmasses.2.2.1 hmasses.2.2.2.2.1 hmasses.2.2.2.2.2 hdegree.2
    (centeredPrimeBands_prime E A W J) (centeredPrimeBands_disjoint E A W J hA.le (by linarith))
    (fun _ hp => centeredPrimePool_lower_nat E A W L J hA.le (by linarith) hend hp)
    (fun p hp => hB p (mem_union_left _ hp))
    hep.1 hep.2.1 hep.2.2.1 hep.2.2.2.1 hep.2.2.2.2
    (fun dq hdq => actualProhibitedPrimeFamily_padding_upper h J ⌊100 * Real.log L⌋₊
      E A W L η eligible hA.le (by linarith) hE hη hηone he hdq)
    (fun w j => centeredPrimeTuple_complement_upper E A W L J hA hW hend w j)
    (fun q hqQ => retainedPrimeDivisor_squarefree Qp (fun _ hp => paddingPrimeSupply_prime hp) (hq q hqQ))
    (fun q hqQ => retainedPrimeDivisor_factors Qp (fun _ hp => paddingPrimeSupply_prime hp) (hq q hqQ))
    actualPaddingCoefficient (actualPaddingVertex Qp) (Real.exp (4 * J))
    (fun d q => (d, q) ∈ data.pairs) (fun _ => actualPaddingDegreeCut Qp L)
    actualPaddingCoefficient_nonneg (fun _ => le_rfl)
    (fun n => by rw [actualPaddingVertex_sq]; exact actualPaddingWeight_one_le Qp n)
    (Real.one_le_exp (by positivity))
    (actualPaddingVertex_residue_congr Qp)
    (fun _ n m hnm => actualPaddingDegreeCut_residue_congr Qp L n m hnm)
    V embed hinj hdim gate (fun _ _ hp => hp)

end TwoPointCorrelations

end OAI
