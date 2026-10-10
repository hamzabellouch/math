import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayHistory

namespace OAI

namespace EditApproximation
namespace BinaryFraction

private theorem history_step_bound (A B k : ℕ) (hB : 0 < B) :
    (1 + (2 * k + 1) * (2 * A + 3)) +
      4 * (1 + (2 * k + 1) * (2 * A + 3)) * B ≤
        (32 * (A + 1)) * (B * (2 * k + 1) + 1) := by
  let F := 1 + (2 * k + 1) * (2 * A + 3)
  have hf : F ≤ 4 * (A + 1) * (2 * k + 1) := by
    dsimp only [F]
    nlinarith only [Nat.zero_le (A * k), Nat.zero_le A, Nat.zero_le k]
  have hn : 2 * k + 1 ≤ B * (2 * k + 1) := Nat.le_mul_of_pos_left _ hB
  have hm := Nat.mul_le_mul_left (4 * (A + 1)) hn
  change F + 4 * F * B ≤ _
  calc
    _ ≤ 4 * (A + 1) * (2 * k + 1) +
        4 * (4 * (A + 1) * (2 * k + 1)) * B := by
      exact Nat.add_le_add hf (Nat.mul_le_mul_right B (Nat.mul_le_mul_left 4 hf))
    _ ≤ 4 * (A + 1) * (B * (2 * k + 1)) +
        4 * (4 * (A + 1) * (2 * k + 1)) * B := Nat.add_le_add_right hm _
    _ = 20 * (A + 1) * (B * (2 * k + 1)) := by ring
    _ ≤ (32 * (A + 1)) * (B * (2 * k + 1) + 1) := by gcongr <;> omega

theorem coarseBinaryArrayHistory_bound {B d : ℕ} {α : Type*} [DecidableEq α]
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
    coarseBinaryArrayHistory k q L frame two tree draws allowance start ≤
      (32 * (A + 1)) * coarseBinaryWeight k q L tree draws allowance := by
  have hkbound : Nat.size k + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      ((coarseLevelMagnitude_ge N k B R).trans (by omega))) _) _).trans hbound
  induction tree generalizing j allowance start with
  | leaf letter =>
    have hb := (coarseBinaryEval_bitWork k q L N R D A frame two (.leaf letter) draws
      hB hq hL htwo htw hd hroot hBbits hqbits hLbits hNbits hbound
      j hdepth allowance start ha hpath hstart).1
    have hs := coarseArrayStorage_le two _ _ D A _ hb
    rw [coarseBinaryArrayHistory, coarseBinaryWeight]
    split_ifs
    · omega
    · have hn : 2 * k + 1 ≤ B * (2 * k + 1) := Nat.le_mul_of_pos_left _ hB
      nlinarith only [hs, hn, Nat.zero_le A, Nat.zero_le k]
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hb := (coarseBinaryEval_bitWork k q L N R D A frame two (.branch children) (draws, below)
      hB hq hL htwo htw hd hroot hBbits hqbits hLbits hNbits hbound
      j hdepth allowance start ha hpath hstart).1
    have hsarray := coarseArrayStorage_le two _ _ D A _ hb
    rw [coarseBinaryArrayHistory, coarseBinaryWeight]
    split_ifs
    · omega
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
      have hc := coarseChildrenArrayHistory_bound k q L N (coarseLevelMagnitude N k B d) D A
        (32 * (A + 1)) two allowance
        (fun child => coarseBinaryEval k q L frame two child)
        (fun child => coarseBinaryArrayHistory k q L frame two child)
        (fun child => coarseBinaryWeight k q L child)
        (List.ofFn fun i => (children i, draws i, below i)) hB (by simp) htwo htw ha.2.2.2.2
        hBbits hqbits hLbits (by omega) (fun draw => (htgrid draw).2.2.2.2) hscale hchildbound (by
          intro child draw childBelow hmem s hs
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact coarseBinaryEval_bitWork k q L N R D A frame two (children i) (below i)
            hB hq hL htwo htw hd hroot hBbits hqbits hLbits hNbits hbound
            (j + 1) (by omega) _ s (hstep (draws i)).1 (hstep (draws i)).2 hs) (by
          intro child draw childBelow hmem s hs
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) (j + 1) (by omega) _ s (hstep (draws i)).1 (hstep (draws i)).2 hs)
        start (by rwa [coarseChildrenSpan_ofFn])
      simp only [List.length_ofFn] at hc
      have hstepCost := history_step_bound A B k hB
      calc
        _ ≤ (1 + (2 * k + 1) * (2 * A + 3)) +
            ((32 * (A + 1)) * coarseBinaryChildrenWeight q L
              (fun child => coarseBinaryWeight k q L child) allowance
              (List.ofFn fun i => (children i, draws i, below i)) +
                4 * (1 + (2 * k + 1) * (2 * A + 3)) * B) := Nat.add_le_add hsarray hc
        _ ≤ (32 * (A + 1)) * coarseBinaryChildrenWeight q L
              (fun child => coarseBinaryWeight k q L child) allowance
              (List.ofFn fun i => (children i, draws i, below i)) +
            (32 * (A + 1)) * (B * (2 * k + 1) + 1) := by omega
        _ = _ := by ring

end BinaryFraction
end EditApproximation

end OAI
