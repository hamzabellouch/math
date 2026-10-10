import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryTemporarySpace
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQuerySetupSpace
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseScratchSpace
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseControlSpace
import OAI.Combinatorics.EditApproximation.Binary.IntegerStoredDataSpace
import OAI.Combinatorics.EditApproximation.Binary.IntegerBinaryWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryFinalSpace
import OAI.Combinatorics.EditApproximation.Probability.RejectionSpace

namespace OAI

namespace EditApproximation
open Filter

/-- Final conversion allocates only its division and clamping workspace. -/
def integerFinalAllocation (source target : List ℤ) (N : ℕ)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) : ℕ :=
  if source.map integerSymbolCode = target.map integerSymbolCode then 0 else
    BinaryFraction.finalAnswerAllocation N
      (computedQueryMemoResult (source.map integerSymbolCode) (target.map integerSymbolCode) N
        (integerOccurrenceIndex source target) (integerInputSymbolBits source target)
        (integerInputPositionBits target) input).value

theorem integerFinalAllocation_le_work (source target : List ℤ) (N : ℕ)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerFinalAllocation source target N input ≤ (integerBinaryOutput source target N input).2 := by
  unfold integerFinalAllocation integerBinaryOutput computedQueryAnswerWithWork
  split
  · exact Nat.zero_le _
  · exact (BinaryFraction.finalAnswerAllocation_le_work _ _).trans (by dsimp only; omega)

/-- Scans and word-RAM preprocessing reserve eight scalar/control cells per
charged step. Retained input/index cells are counted separately. Numerical
setup, local programs and coarse initialization use their explicit allocation
counters. Streaming samplers reuse a bounded buffer, without storing failed
trial counts or failed words. -/
noncomputable def integerAcceptedSpaceTerms (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) : List ℕ :=
  let x := source.map integerSymbolCode
  let y := target.map integerSymbolCode
  [8 * integerPreevaluationWork source target N epsilon,
   2 * integerStoredDataSpace source target,
   computedQuerySetupAllocation N,
   (computedQueryMemoResult x y N (integerOccurrenceIndex source target)
     (integerInputSymbolBits source target) (integerInputPositionBits target) input).memory.fractionStorage,
   computedQueryTemporaryCells x y N (integerOccurrenceIndex source target)
     (integerInputSymbolBits source target) (integerInputPositionBits target) input,
   computedFamilyCoarseCopyStorage x y N input,
   computedFamilyCoarseArrayCapacity x y N input,
   computedFamilyCoarseScratchCapacity x y N input,
   computedFamilyCoarseControlCapacity x y N input,
   4 * (inputHeight N + (integerParameters N).B + 4),
   integerFinalAllocation source target N input,
   8 * (N + 1)]

/-- The space bound applies to all outcomes, including null-probability
outcomes. The exact branch uses the concrete suffix-DP allocation counter. -/
noncomputable def integerBinarySpace (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) : ℕ :=
  if physicalLargeInput N epsilon then
    match outcome with
    | .inl _ => 8 * integerPreevaluationWork source target N epsilon +
        2 * integerStoredDataSpace source target +
        suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1)
    | .inr execution => (integerAcceptedSpaceTerms source target N epsilon
        (computedExecutionAccepted _ _ N execution)).sum
  else 8 * integerPreevaluationWork source target N epsilon +
    2 * integerStoredDataSpace source target +
    suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1)

private theorem sum_cells_le (values : List ℕ) (B : ℕ) (h : ∀ x ∈ values, x ≤ B) :
    values.sum ≤ values.length * B := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem embed_space_power (X K e a : ℕ) (hX : 2 ≤ X) (he : e ≤ K) (ha : a ≤ X ^ e) :
    a ≤ X ^ K := ha.trans (Nat.pow_le_pow_right (by omega) he)

private theorem bounded_space_sum (X K : ℕ) (terms : List ℕ) (hX : 2 ≤ X)
    (hl : terms.length ≤ 16) (ht : ∀ a ∈ terms, a ≤ X ^ K) :
    terms.sum ≤ X ^ (K + 4) := by
  have hs := sum_cells_le terms (X ^ K) ht
  have h16 : 16 ≤ X ^ 4 := (by decide : 16 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hX 4)
  calc
    _ ≤ terms.length * X ^ K := hs
    _ ≤ X ^ 4 * X ^ K := Nat.mul_le_mul_right _ (hl.trans h16)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem integerBinarySpace_polynomial (C : ℕ) (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ outcome, integerBinarySpace source target N epsilon outcome ≤ (N + 2) ^ (C + 65564) := by
  filter_upwards [physicalLargeInput_eventually epsilon hepsilon,
    integerPreevaluationWork_near_linear C 1 (by norm_num), integerStoredDataSpace_polynomial C,
    integerQueryWidths C, computedQueryTemporaryCells_polynomial, integer_encoded_symbol_bits C,
    computedFamilyCoarseCopyStorage_polynomial, computedFamilyCoarseArrayCapacity_polynomial,
    computedFamilyCoarseScratchCapacity_polynomial, computedFamilyCoarseControlCapacity_polynomial]
    with N hlarge hpre hstored hwidth htemp hsymbols hcopy harray hscratch hcontrol
  intro source target hsize halphabet outcome
  let X := N + 2
  let K := C + 65560
  change _ ≤ X ^ (C + 65564)
  rw [← show K + 4 = C + 65564 by dsimp only [K]]
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hN := largeAccuracyInput_pos N epsilon.value hlarge.2.1
  have hell := hlarge.2.1.1
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hsz : (source.map integerSymbolCode).length + (target.map integerSymbolCode).length ≤ N := by
    simpa only [List.length_map] using hsize
  have hs (a) (ha : a ∈ source.map integerSymbolCode) : a < 2 ^ integerInputSymbolBits source target := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_left _ hz)
  have ht (a) (ha : a ∈ target.map integerSymbolCode) : a < 2 ^ integerInputSymbolBits source target := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_right _ hz)
  have hp : (target.map integerSymbolCode).length ≤ 2 ^ integerInputPositionBits target := by
    simpa only [List.length_map, integerInputPositionBits] using (Nat.lt_size_self target.length).le
  have hpre2 : integerPreevaluationWork source target N epsilon ≤ X ^ 2 := by
    have h := hpre source target hsize halphabet epsilon
    norm_num at h
    exact_mod_cast h
  have hpreK : 8 * integerPreevaluationWork source target N epsilon ≤ X ^ K := by
    apply embed_space_power X K 5 _ hX (by dsimp only [K]; omega)
    calc
      _ ≤ X ^ 3 * X ^ 2 := Nat.mul_le_mul ((by decide : 8 ≤ (2 : ℕ) ^ 3).trans
        (Nat.pow_le_pow_left hX 3)) hpre2
      _ = _ := by rw [← pow_add]
  have hstoredK : 2 * integerStoredDataSpace source target ≤ X ^ K := by
    apply embed_space_power X K (C + 23) _ hX (by dsimp only [K]; omega)
    calc
      _ ≤ X * X ^ (C + 22) := Nat.mul_le_mul hX (hstored source target hsize halphabet)
      _ = _ := by rw [← pow_succ']
  have hlinearK : 8 * (N + 1) ≤ X ^ K := by
    apply embed_space_power X K 4 _ hX (by dsimp only [K]; omega)
    calc
      _ ≤ X ^ 3 * X := Nat.mul_le_mul ((by decide : 8 ≤ (2 : ℕ) ^ 3).trans
        (Nat.pow_le_pow_left hX 3)) (by dsimp only [X]; omega)
      _ = _ := by rw [← pow_succ]
  have hdpK : suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) ≤ X ^ K := by
    apply embed_space_power X K 10 _ hX (by dsimp only [K]; omega)
    calc
      _ ≤ 50 * (N + 1) ^ 4 := suffixDPAllocation_polynomial _ _ N hsz
      _ ≤ X ^ 6 * X ^ 4 := Nat.mul_le_mul ((by decide : 50 ≤ (2 : ℕ) ^ 6).trans
        (Nat.pow_le_pow_left hX 6)) (Nat.pow_le_pow_left (by dsimp only [X]; omega) 4)
      _ = _ := by rw [← pow_add]
  have hfallback : 8 * integerPreevaluationWork source target N epsilon +
      2 * integerStoredDataSpace source target +
      suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1) ≤
      X ^ (K + 4) := by
    have hu : 4 ≤ X ^ 4 := (by decide : 4 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hX 4)
    calc
      _ ≤ 4 * X ^ K := by omega
      _ ≤ X ^ 4 * X ^ K := Nat.mul_le_mul_right _ hu
      _ = _ := by rw [← pow_add, Nat.add_comm 4 K]
  simp only [integerBinarySpace, hlarge, ite_true]
  cases outcome with
  | inl unitValue => exact hfallback
  | inr execution =>
    let input := computedExecutionAccepted (source.map integerSymbolCode) (target.map integerSymbolCode) N execution
    have hwidths := hwidth source target hsize halphabet
    have hmemo := computedQueryMemoResult_storage (source.map integerSymbolCode) (target.map integerSymbolCode) N
      (integerOccurrenceIndex source target) (integerInputSymbolBits source target) (integerInputPositionBits target)
      input hN hell hf hsz hlarge.2.2 hs ht hp rfl
    have htmp := htemp (source.map integerSymbolCode) (target.map integerSymbolCode) hsz input
      (integerOccurrenceIndex source target) (integerInputSymbolBits source target) (integerInputPositionBits target)
      hwidths.1 hwidths.2 hs ht hp rfl
    have hset := (computedQuerySetupAllocation_le_work N).trans (computedQuerySetupWithWork_cost N hN hell)
    have hH48 : inputHeight N ^ 12 ≤ X ^ 48 :=
      (Nat.pow_le_pow_left (computed_height_polynomial N) 12).trans_eq (by rw [← pow_mul])
    have hsetupK := embed_space_power X K 48 _ hX (by dsimp only [K]; omega) (hset.trans hH48)
    have hmemoK := embed_space_power (N + 2) K 65557
      (computedQueryMemoResult (source.map integerSymbolCode) (target.map integerSymbolCode) N
        (integerOccurrenceIndex source target) (integerInputSymbolBits source target)
        (integerInputPositionBits target) input).memory.fractionStorage hX
      ((by decide : 65557 ≤ 65560).trans (Nat.le_add_left 65560 C)) hmemo
    have htmpK := embed_space_power X K 20 _ hX (by dsimp only [K]; omega) htmp
    have hcopyK := embed_space_power X K 18 _ hX (by dsimp only [K]; omega)
      (hcopy _ _ hsz (hsymbols source target halphabet) input)
    have harrayK := embed_space_power X K 39 _ hX (by dsimp only [K]; omega) (harray _ _ hsz input)
    have hscratchK := embed_space_power X K 183 _ hX (by dsimp only [K]; omega) (hscratch _ _ hsz input)
    have hcontrolK := embed_space_power X K 184 _ hX (by dsimp only [K]; omega) (hcontrol _ _ hsz input)
    have hbufferK : 4 * (inputHeight N + (integerParameters N).B + 4) ≤ X ^ K := by
      have hH : inputHeight N ≤ X ^ 4 := computed_height_polynomial N
      have hB : (integerParameters N).B ≤ X ^ 4 :=
        BinaryFraction.computedCoarseBranching_polynomial N hN
          (two_hundred_le_two_pow_thousand.trans hell)
      have h4 : 4 ≤ X ^ 4 := (by decide : 4 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hX 4)
      have h16 : 16 ≤ X ^ 4 := (by decide : 16 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hX 4)
      apply embed_space_power X K 8 _ hX (by dsimp only [K]; omega)
      calc
        _ ≤ 4 * (X ^ 4 + X ^ 4 + X ^ 4) :=
          Nat.mul_le_mul_left 4 (Nat.add_le_add (Nat.add_le_add hH hB) h4)
        _ = 12 * X ^ 4 := by ring
        _ ≤ 16 * X ^ 4 := Nat.mul_le_mul_right _ (by decide : 12 ≤ 16)
        _ ≤ X ^ 4 * X ^ 4 := Nat.mul_le_mul_right _ h16
        _ = _ := by rw [← pow_add]
    have houtK : integerFinalAllocation source target N input ≤ X ^ K := by
      have hout := (integerFinalAllocation_le_work source target N input).trans
        (integerBinaryOutput_cost source target N epsilon hlarge hsize input)
      have hH40 : inputHeight N ^ 10 ≤ X ^ 40 :=
        (Nat.pow_le_pow_left (computed_height_polynomial N) 10).trans_eq (by rw [← pow_mul])
      have hn : N ≤ X ^ 40 := (by dsimp only [X]; omega : N ≤ X).trans (Nat.le_pow (by decide))
      apply embed_space_power X K 41 _ hX (by dsimp only [K]; omega)
      calc
        _ ≤ 2 * X ^ 40 := by omega
        _ ≤ X * X ^ 40 := Nat.mul_le_mul_right _ hX
        _ = _ := by rw [← pow_succ']
    apply bounded_space_sum X K _ hX (by change 12 ≤ 16; decide)
    intro a ha
    simp only [integerAcceptedSpaceTerms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpreK
    · exact hstoredK
    · exact hsetupK
    · exact hmemoK
    · exact htmpK
    · exact hcopyK
    · exact harrayK
    · exact hscratchK
    · exact hcontrolK
    · exact hbufferK
    · exact houtK
    · exact hlinearK

end EditApproximation

end OAI
