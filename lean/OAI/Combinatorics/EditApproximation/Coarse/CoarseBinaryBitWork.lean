import OAI.Combinatorics.EditApproximation.Coarse.CoarseLevelMagnitude

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Actual Boolean work of the complete pruning-stopped evaluator. The
hypotheses bound input registers and the common grid, not execution cost. -/
 theorem coarseBinaryEval_bitWork {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N R D A : ℕ) (frame : List (Option α)) (two : BinaryFraction)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (htwo : two.value = 2)
    (htw : two.width ≤ A) (hd : Nat.size two.representation.den ≤ D)
    (hroot : two.representation.den = coarseCommonDenominator 1 q L B R)
    (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
    (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
    (hbound : Nat.size (coarseLevelMagnitude N k B R + 2) + 2 * D + 1 ≤ A)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction) (start : ℕ)
    (ha : CoarseGridCell two allowance k D A)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j)
    (hstart : start + tree.word.length ≤ N) :
    CoarseBinaryBox two (2 * k + 1) (coarseLevelMagnitude N k B d) D A
      (coarseBinaryEval k q L frame two tree draws allowance start).1 ∧
    (coarseBinaryEval k q L frame two tree draws allowance start).2 ≤
      (100000000 * (A + 1) ^ 2) * coarseBinaryWeight k q L tree draws allowance := by
  have hkbound : Nat.size k + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      ((coarseLevelMagnitude_ge N k B R).trans (by omega))) _) _).trans hbound
  induction tree generalizing j allowance start with
  | leaf letter =>
    have hnat : (nat (CoarseSourceTree.leaf (B := B) letter).word.length).width ≤ A :=
      (nat_width_le _).trans ((Nat.add_le_add_right (Nat.size_le_size (by omega)) 2).trans hNbits)
    have hp := leWithWork_cost (nat (CoarseSourceTree.leaf (B := B) letter).word.length) allowance A hnat ha.2.2.2.2
    have hs : Nat.size (CoarseSourceTree.leaf (B := B) letter).word.length ≤ A :=
      (Nat.size_le_size (show (CoarseSourceTree.leaf (B := B) letter).word.length ≤ N by omega)).trans (by omega)
    rw [coarseBinaryEval, coarseBinaryWeight]
    split_ifs
    · exact ⟨coarseBinaryBox_none _ _ _ _ _, by dsimp only; nlinarith only [hp, hs, Nat.zero_le A]⟩
    · have hvbound : Nat.size (coarseLevelMagnitude N k B 0) + 2 * D + 1 ≤ A :=
        (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
          ((coarseLevelMagnitude_mono N k B 0 R (by omega)).trans (by omega))) _) _).trans hbound
      have hcell (shift : Fin (2 * k + 1)) :
          CoarseGridCell two (coarseGridNatWithWork allowance.denominator allowance.denominator_pos
            (coarseShiftCost k frame (.leaf (B := B) letter) start shift)).1
            (coarseLevelMagnitude N k B 0) D A := by
        apply coarseGridNatWithWork_bounds two _ _ _ _ _ _ ha.1 ha.2.1 _ hvbound
        have hcost : coarseShiftCost k frame (.leaf (B := B) letter) start shift ≤ 1 := by
          cases letter <;> simp only [coarseShiftCost] <;> (try split_ifs) <;> omega
        exact hcost.trans (coarseLevelMagnitude_pos N k B 0)
      constructor
      · intro cells hc
        have heq : (arithmeticMapWithWork (fun shift : Fin (2 * k + 1) =>
            coarseGridNatWithWork allowance.denominator allowance.denominator_pos
              (coarseShiftCost k frame (.leaf (B := B) letter) start shift))
            (List.finRange (2 * k + 1))).1 = cells := Option.some.inj hc
        rw [← heq, arithmeticMapWithWork_value]
        refine ⟨by simp, ?_⟩
        intro a hamem
        obtain ⟨shift, _, rfl⟩ := List.mem_map.mp hamem
        exact hcell shift
      · have hc := arithmeticMapWithWork_cost (fun shift : Fin (2 * k + 1) =>
            coarseGridNatWithWork allowance.denominator allowance.denominator_pos
              (coarseShiftCost k frame (.leaf (B := B) letter) start shift))
            (List.finRange (2 * k + 1)) (100 * (A + 1) ^ 2) (by
          intro shift _
          apply coarseGridNatWithWork_cost _ _ _ A _ ((le_max_right _ _).trans ha.2.2.2.2)
          have hcost : coarseShiftCost k frame (.leaf (B := B) letter) start shift ≤ 1 := by
            cases letter <;> simp only [coarseShiftCost] <;> (try split_ifs) <;> omega
          exact (Nat.size_le_size hcost).trans (by norm_num; omega))
        simp only [List.length_finRange] at hc
        have hBn : 2 * k + 1 ≤ B * (2 * k + 1) := by nlinarith
        have hbudget := Nat.mul_le_mul_left ((A + 1) ^ 2) hBn
        have hunit : 1 ≤ (A + 1) ^ 2 := by
          have hz : 0 < (A + 1) ^ 2 := by positivity
          omega
        have hnscale := Nat.mul_le_mul_right (2 * k + 1) hunit
        dsimp only
        nlinarith only [hp, hs, hc, hbudget, hnscale, Nat.zero_le A, Nat.zero_le k]
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hnat : (nat (CoarseSourceTree.branch children).word.length).width ≤ A :=
      (nat_width_le _).trans ((Nat.add_le_add_right (Nat.size_le_size (by omega)) 2).trans hNbits)
    have hp := leWithWork_cost (nat (CoarseSourceTree.branch children).word.length) allowance A hnat ha.2.2.2.2
    have hslen : Nat.size (CoarseSourceTree.branch children).word.length ≤ A :=
      (Nat.size_le_size (show (CoarseSourceTree.branch children).word.length ≤ N by omega)).trans (by omega)
    rw [coarseBinaryEval, coarseBinaryWeight]
    split_ifs
    · exact ⟨coarseBinaryBox_none _ _ _ _ _, by dsimp only; nlinarith only [hp, hslen, Nat.zero_le A]⟩
    · have htval (draw : Fin B) : (coarseChildThresholdWithWork B q allowance draw).1.value =
          coarseChildThreshold B q allowance.value draw := by
        apply coarseChildThresholdWithWork_value
        rw [ha.1, hroot, ← hdepth]
        exact coarseThreshold_root_grid B q L j d allowance.value draw hB hq hpath
      have htgrid (draw : Fin B) : CoarseGridCell two
          (coarseChildThresholdWithWork B q allowance draw).1 k D A := by
        apply coarseChildThresholdWithWork_bounds two allowance B q k D A draw hq ha hd _ hkbound
        rw [ha.1, hroot, ← hdepth]
        exact coarseThreshold_root_grid B q L j d allowance.value draw hB hq hpath
      have hscale : CoarseGridCell two (coarseChildAllowanceWithWork q allowance).1 k D A := by
        apply coarseChildAllowanceWithWork_bounds two allowance q k D A hq ha hd _ hkbound
        rw [ha.1, hroot, ← hdepth]
        exact coarseScale_root_grid B q L j (d + 1) allowance.value hq hpath
      have hstep (draw : Fin B) :
          CoarseGridCell two (coarseChildAllowanceWithWork L
            (coarseChildThresholdWithWork B q allowance draw).1).1 k D A ∧
          (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1.value.den ∣
            (L * B * q) ^ (j + 1) := by
        let threshold := (coarseChildThresholdWithWork B q allowance draw).1
        have hden : (threshold.value / L).den ∣ threshold.representation.den := by
          rw [htval draw, (htgrid draw).1, hroot, ← hdepth]
          rw [show coarseChildThreshold B q allowance.value draw / (L : ℚ) =
            (1 / (L : ℚ)) * coarseChildThreshold B q allowance.value draw by ring]
          exact coarseChildAllowance_root_grid B q L j d allowance.value draw hB hq hL hpath
        refine ⟨coarseChildAllowanceWithWork_bounds two threshold L k D A hL (htgrid draw) hd hden hkbound, ?_⟩
        rw [coarseChildAllowanceWithWork_value L threshold hden, htval draw]
        convert coarseChildAllowance_grid B q L j allowance.value draw hB hq hL hpath using 1
        congr 1
        ring
      have hchildbound : Nat.size (B * (coarseLevelMagnitude N k B d + k) + 2) + 2 * D + 1 ≤ A := by
        apply le_trans _ hbound
        apply Nat.add_le_add_right
        apply Nat.add_le_add_right
        apply Nat.size_le_size
        exact (coarseLevelMagnitude_succ N k B d).trans
          ((coarseLevelMagnitude_mono N k B (d + 1) R (by omega)).trans (by omega))
      have hc := coarseBinaryChildren_bounds k q L N (coarseLevelMagnitude N k B d) D A two allowance
        (fun child => coarseBinaryEval k q L frame two child)
        (fun child => coarseBinaryWeight k q L child)
        (List.ofFn fun i => (children i, draws i, below i)) hB (by simp) htwo htw ha.2.2.2.2
        hBbits hqbits hLbits (by omega) (fun draw => (htgrid draw).2.2.2.2) hscale hchildbound (by
          intro child draw childBelow hmem s hs
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) (j + 1) (by omega) _ s (hstep (draws i)).1 (hstep (draws i)).2 hs)
        start (by rwa [coarseChildrenSpan_ofFn])
      constructor
      · have hm : (List.ofFn fun i => (children i, draws i, below i)).length *
            (coarseLevelMagnitude N k B d + k) ≤ coarseLevelMagnitude N k B (d + 1) := by
          simp only [List.length_ofFn]
          exact (Nat.le_add_right _ 2).trans (coarseLevelMagnitude_succ N k B d)
        exact coarseBinaryBox_mono two (2 * k + 1) _ _ D A _ hc.1 hm
      · have hcost := hc.2
        simp only [List.length_ofFn] at hcost
        have hprune : (leWithWork (nat (CoarseSourceTree.branch children).word.length) allowance).2 +
            Nat.size (CoarseSourceTree.branch children).word.length + 1 ≤ 100000000 * (A + 1) ^ 2 := by
          nlinarith only [hp, hslen, Nat.zero_le A]
        dsimp only
        nlinarith only [hcost, hprune]

end BinaryFraction
end EditApproximation

end OAI
