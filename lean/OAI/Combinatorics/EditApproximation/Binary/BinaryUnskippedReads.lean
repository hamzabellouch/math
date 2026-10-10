import OAI.Combinatorics.EditApproximation.Binary.BinaryBandReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedUnskipped

namespace OAI

/-! The accepted-band record is built from the reader-aware tests.
Only proof fields are erased; numerical tests and reads remain charged. -/

namespace EditApproximation
namespace BinaryFraction

private theorem rounded_action_congr {n M : ℕ} (e b : ℕ)
    {first second : List (Fin M → TargetInterval n)} (h : first = second)
    (hf : first ≠ []) (hs : second ≠ []) (initial : Fin M → TargetInterval n → ℚ) :
    canonicalRoundedBandAction e b first hf initial = canonicalRoundedBandAction e b second hs initial := by
  subst second
  rfl

def preparedUnskippedReadWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    Option (UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (read i q).1.value) (fun i q => (initial i q).1.value)) × ℕ :=
  let band := preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) read
  if hband : band.1 = [] then (none, band.2 + 1) else
    let wide := wideActionGridWithWork M parent center b P
    let guard := unskippedGuardReadWithWork parent center b exponent F band.1
      (wide.1.map Vector.get) hband initial
    if hguard : guard.1 = true then
      let hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F band.1
        (wide.1.map Vector.get) hband initial C hi).1
      let facts := (unskippedGuardWithWork_value source target parent center b exponent F
        band.1 (wide.1.map Vector.get) hband (fun i q => (initial i q).1) hb).mp (hg.symm.trans hguard)
      let hbandValue : band.1 = representativeBandActions source target parent center b P tau.value
          ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (read i q).1.value) := by
        apply (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo) b P
          tau (inversePowerTwo exponent) read R hr).1.trans
        simpa only [inversePowerTwo_value] using preparedRepresentativeWithWork_value source target
          parent center b P hP tau (inversePowerTwo exponent) (fun i q => (read i q).1)
      let hwideValue : wide.1.map Vector.get = wideActionList M parent center b P :=
        wideActionGridWithWork_value M parent center b P hP
      (some {
        center := center
        nonempty := fun hzero => hband (hbandValue.trans hzero)
        sum_guard := by simpa only [hbandValue] using facts.1
        wide_guard := by
          have hw := facts.2.1
          rw [hwideValue] at hw
          rw [rounded_action_congr exponent b hbandValue hband _] at hw
          exact hw
        imbalance_guard := by simpa only [hbandValue] using facts.2.2 },
        band.2 + wide.2 + guard.2 + wide.1.length + 3)
    else (none, band.2 + wide.2 + guard.2 + wide.1.length + 2)

theorem preparedUnskippedReadWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).1 =
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).1 := by
  have hband := (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr).1
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband]
  split_ifs with hempty hguard
  · rfl
  · rfl
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hplain (hg.symm.trans hguard))
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hguard (hg.trans hplain))
  · rfl


theorem preparedUnskippedReadWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).2 ≤
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).2 +
      representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
      M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1.length * (C + 3)) +
      M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1.length * (C + 3)) := by
  have hband := preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband.1]
  by_cases hempty : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1 = []
  · simp only [dite_eq_left hempty]
    omega
  · simp only [dite_eq_right hempty]
    have hg := unskippedGuardReadWithWork_eq_cost parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi
    simp only [hg.1]
    split_ifs <;> omega

end BinaryFraction
end EditApproximation

end OAI
