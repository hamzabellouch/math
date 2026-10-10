import OAI.Combinatorics.EditApproximation.Coarse.CoarseChildrenSimulation

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Every binary array cell equals the rational shared evaluator, including
all pruning outcomes. The sole invariant is the explicitly constructed root
denominator and the literal path's allowance denominator. -/
 theorem coarseBinaryEval_rep {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L D : ℕ) (frame : List (Option α)) (two : BinaryFraction)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (htwo : two.value = 2)
    (hroot : two.representation.den = coarseCommonDenominator 1 q L B D)
    (j : ℕ) (hdepth : j + d = D) (allowance : BinaryFraction) (start : ℕ)
    (ha : allowance.representation.den = two.representation.den)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j) :
    CoarseArrayRep (coarseBinaryEval k q L frame two tree draws allowance start).1
      (coarseArrayEval k q (1 / L) frame tree draws allowance.value start).1 := by
  induction tree generalizing j allowance start with
  | leaf letter =>
    have hp := leWithWork_value (nat (CoarseSourceTree.leaf (B := B) letter).word.length) allowance
    rw [nat_value] at hp
    rw [coarseBinaryEval, coarseArrayEval]
    by_cases hprune : ((CoarseSourceTree.leaf (B := B) letter).word.length : ℚ) ≤ allowance.value
    · rw [ite_eq_left (hp.mpr hprune), ite_eq_left hprune]
      rfl
    · have hb : ¬ (leWithWork (nat (CoarseSourceTree.leaf (B := B) letter).word.length) allowance).1 = true :=
        fun h => hprune (hp.mp h)
      rw [ite_eq_right hb, ite_eq_right hprune]
      simp only [CoarseArrayRep, coarseBinaryContents, coarseRationalContents, Option.map_some,
        arithmeticMapWithWork_value, List.map_map, Function.comp_def,
        coarseGridNatWithWork_value, coarseStoredOfFn, List.ofFn_eq_map]
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hp := leWithWork_value (nat (CoarseSourceTree.branch children).word.length) allowance
    rw [nat_value] at hp
    rw [coarseBinaryEval, coarseArrayEval]
    by_cases hprune : ((CoarseSourceTree.branch children).word.length : ℚ) ≤ allowance.value
    · rw [ite_eq_left (hp.mpr hprune), ite_eq_left hprune]
      rfl
    · have hb : ¬ (leWithWork (nat (CoarseSourceTree.branch children).word.length) allowance).1 = true :=
        fun h => hprune (hp.mp h)
      rw [ite_eq_right hb, ite_eq_right hprune]
      have ht (draw : Fin B) : (coarseChildThresholdWithWork B q allowance draw).1.value =
          coarseChildThreshold B q allowance.value draw := by
        apply coarseChildThresholdWithWork_value
        rw [ha, hroot, ← hdepth]
        exact coarseThreshold_root_grid B q L j d allowance.value draw hB hq hpath
      have hs : (coarseChildAllowanceWithWork q allowance).1.value = allowance.value / q := by
        apply coarseChildAllowanceWithWork_value
        rw [ha, hroot, ← hdepth]
        exact coarseScale_root_grid B q L j (d + 1) allowance.value hq hpath
      apply coarseBinaryChildren_rep k q L frame two allowance _ htwo ha ht hs
      intro child draw childBelow hmem s
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
      cases hi
      let threshold := coarseChildThresholdWithWork B q allowance (draws i)
      let childAllowance := coarseChildAllowanceWithWork L threshold.1
      have htd : threshold.1.representation.den = two.representation.den :=
        (coarseChildThresholdWithWork_den B q allowance (draws i)).trans ha
      have had : childAllowance.1.representation.den = two.representation.den :=
        (coarseChildAllowanceWithWork_den L threshold.1).trans htd
      have hav : childAllowance.1.value = (1 / (L : ℚ)) *
          coarseChildThreshold B q allowance.value (draws i) := by
        have hg : (threshold.1.value / L).den ∣ threshold.1.representation.den := by
          rw [ht (draws i), htd, hroot, ← hdepth]
          rw [show coarseChildThreshold B q allowance.value (draws i) / (L : ℚ) =
            (1 / (L : ℚ)) * coarseChildThreshold B q allowance.value (draws i) by ring]
          exact coarseChildAllowance_root_grid B q L j d allowance.value (draws i) hB hq hL hpath
        have hv := coarseChildAllowanceWithWork_value L threshold.1 hg
        change childAllowance.1.value = _ at hv ⊢
        rw [hv, ht (draws i)]
        ring
      have hap : childAllowance.1.value.den ∣ (L * B * q) ^ (j + 1) := by
        rw [hav]
        exact coarseChildAllowance_grid B q L j allowance.value (draws i) hB hq hL hpath
      have hrec := ih i (below i) (j + 1) (by omega) childAllowance.1 s had hap
      rw [hav] at hrec
      exact hrec

end BinaryFraction
end EditApproximation

end OAI
