import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.ActualBlockTrace
import OAI.NumberTheory.TwoPoint.Bounds.PrimeAlphabetSize
import OAI.NumberTheory.TwoPoint.Bounds.TraceIntervalError

namespace OAI

/-! The actual masked matrix on every sufficiently long integer interval.
The error includes all initial vertices and both paths of the trace. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_interval_matrix
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => matrixFrobeniusSq
        (shiftMatrix (primeBlockEmbedding (P := P) ⌈Real.exp (103 * L)⌉₊)
          (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
          (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
            (fun t n => weight t (n + (a + x.val : ℕ)))) ^ ⌊L⌋₊)) ≤
        (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) + 1 := by
  obtain ⟨A, hA, hword⟩ := hprime.eventually_actual_prime_word_comparison hBr h E hE W hW
  refine ⟨A, hA, ?_⟩
  filter_upwards [hword, hprime.eventually_actual_block_trace h hh E hE W hW,
    eventually_ge_atTop (4800 : ℝ)] with L hword htrace hlarge
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
  let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
    (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
    (fun _ => actualPaddingDegreeCut Qp L) h
    (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
  let D := (j : Fin J) → P j
  let M := ⌈Real.exp (103 * L)⌉₊
  let V := D × Fin M
  let embed : V → D × ℤ := primeBlockEmbedding M
  let tuple : D → ℕ := fun d => ∏ j, (d j).val
  have hprimeP := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hdisjoint := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hP (j : Fin J) : P j ⊆ data.P := centeredPrimeBand_subset_pool E _ W J j
  have hsq (q : ℕ) (hq : q ∈ Q) : Squarefree q :=
    retainedPrimeDivisor_squarefree Qp (fun _ hp => paddingPrimeSupply_prime hp) (mem_filter.mp hq).1
  have hpool (q : ℕ) (hq : q ∈ Q) : q.primeFactors ⊆ data.Q :=
    retainedPrimeDivisor_factors Qp (fun _ hp => paddingPrimeSupply_prime hp) (mem_filter.mp hq).1
  intro gate a N hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
    exact_mod_cast this
  let : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hcompare := physicalMatrix_moment_comparison embed
    (primeBlockEmbedding_injective M) Q tuple h gate weight
    (maskedSignedIntegerWeight_flip Q actualPaddingCoefficient _ _ _ _ _ _ h _)
    (FiniteLaw.uniform (Fin N)) (data.residueLaw ⌊Real.exp L⌋₊ hB)
    (fun x => (a + x.val : ℕ)) data.residueOrigin ⌊L⌋₊ (Real.exp (-(L ^ 9)))
    (Real.exp_pos _).le ?_
  · rw [FiniteLaw.uniform_average] at hcompare
    have herr := trace_interval_error_le_one L ⌊L⌋₊ (Fintype.card V)
      (Fintype.card (D × (Q × Bool))) hlarge (Nat.floor_le (by linarith))
      (Nat.cast_nonneg _) (actual_prime_block_dimension E W L hW hL)
      (actual_prime_alphabet_size E W L hW hlarge)
    have hupper := htrace hL η hη hηone eligible he gate
    have hdiff := (le_abs_self _).trans (hcompare.trans herr)
    dsimp only [embed, V, D, tuple, M, weight, data, Q, Qp, P, J] at hdiff
    linarith
  · intro i b c hend
    let enc := closedTraceEncoding Q (b, c)
    have hclosed : wordDisplacement h (columnTupleWord enc.2.1 enc.1 (fun j => (enc.2.2 j).val)) = 0 := by
      rw [closedTraceEncoding_word]
      exact integer_closed_word_displacement Q tuple h (embed i) b c hend
    have hw := hword hL η hη hηone eligible he enc.2.1 enc.1 enc.2.2 hclosed
      (a + i.2.val) N hN
    rw [closedTraceEncoding_word] at hw
    have ht := data.residue_average_translate hB
      (fun n => scalarWalkProduct h weight n (integerClosedWordCode Q tuple (b, c)))
      (fun n m hnm => scalarWalkProduct_residue_congr (data.P ∪ data.Q) h weight _
        (fun t ht z z' hz => primeClosedPair_residue_congr data hB hP hprimeP hdisjoint
          ⌊L ^ (1 / 10 : ℝ)⌋₊ Q actualPaddingCoefficient (fun d q => (d, q) ∈ data.pairs)
          (actualPaddingVertex Qp) L (Real.exp (4 * J)) (fun _ => actualPaddingDegreeCut Qp L)
          hsq hpool (actualPaddingVertex_residue_congr Qp)
          (fun _ n m hnm => actualPaddingDegreeCut_residue_congr Qp L n m hnm)
          b c t ht z z' (fun p => hz p.val p.property)) n m (fun p hp => hnm ⟨p, hp⟩))
      (embed i).2
    have havg : (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r =>
        scalarWalkProduct h weight ((embed i).2 + data.residueOrigin r)
          (integerClosedWordCode Q tuple (b, c))) =
        (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r =>
          scalarWalkProduct h weight (data.residueOrigin r)
            (integerClosedWordCode Q tuple (b, c))) := by
      simpa only [add_comm (embed i).2] using ht
    rw [FiniteLaw.uniform_average]
    rw [havg]
    simpa only [embed, primeBlockEmbedding, Nat.cast_add,
      add_assoc, add_left_comm (a : ℤ)] using hw

end TwoPointCorrelations

end OAI
