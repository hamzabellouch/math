import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedKernel

namespace OAI

/-! Successful binary guard evaluation constructs exactly the tested record
used by group sampling. Proof fields carry no runtime cost. -/

namespace EditApproximation
namespace BinaryFraction

private theorem rounded_band_congr {ny M : ℕ} (e b : ℕ)
    {first second : List (Fin M → TargetInterval ny)} (h : first = second)
    (hf : first ≠ []) (hs : second ≠ []) (initial : Fin M → TargetInterval ny → ℚ) :
    canonicalRoundedBandAction e b first hf initial =
      canonicalRoundedBandAction e b second hs initial := by
  subst second
  rfl

def unskippedCandidateWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (hb : 0 < b)
    (tau F : BinaryFraction) (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (center : TargetInterval target.length) :
    Option (UnskippedBand source target parent b P thetaExponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).value)) × ℕ :=
  let band := representativeBandWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo thetaExponent) child
  if hband : band.1 = [] then (none, band.2 + 1) else
    let wide := materializedWideActionsWithWork M parent center b P
    let guard := unskippedGuardWithWork parent center b thetaExponent F band.1
      (wide.1.map Vector.get) hband initial
    if hguard : guard.1 = true then
      let facts := (unskippedGuardWithWork_value source target parent center b thetaExponent F
        band.1 (wide.1.map Vector.get) hband initial hb).mp hguard
      let hbandValue : band.1 = representativeBandActions source target parent center b P tau.value
          ((2 : ℚ) ^ (-(thetaExponent : ℤ))) (fun i q => (child i q).value) := by
        simpa only [inversePowerTwo_value] using representativeBandWithWork_value source target parent center b P
          tau (inversePowerTwo thetaExponent) child
      let hwideValue : wide.1.map Vector.get = wideActionList M parent center b P :=
        materializedWideActionsWithWork_value M parent center b P
      (some {
        center := center
        nonempty := by
          intro hzero
          apply hband
          exact hbandValue.trans hzero
        sum_guard := by
          simpa only [hbandValue] using facts.1
        wide_guard := by
          have hw := facts.2.1
          rw [hwideValue] at hw
          rw [rounded_band_congr thetaExponent b hbandValue hband _] at hw
          exact hw
        imbalance_guard := by
          simpa only [hbandValue] using facts.2.2 },
        band.2 + wide.2 + guard.2 + wide.1.length + 3)
    else (none, band.2 + wide.2 + guard.2 + wide.1.length + 2)

@[simp] theorem unskippedCandidateWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (hb : 0 < b)
    (tau F : BinaryFraction) (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (center : TargetInterval target.length) :
    (unskippedCandidateWithWork source target parent b P thetaExponent hb tau F child initial center).1 =
      testUnskippedBand source target parent b P thetaExponent tau.value F.value
        (fun i q => (child i q).value) (fun i q => (initial i q).value) center := by
  let band := representativeBandActions source target parent center b P tau.value
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) (fun i q => (child i q).value)
  have hbandValue : (representativeBandWithWork parent center (parent.hi - parent.lo) b P
      tau (inversePowerTwo thetaExponent) child).1 = band := by
    simpa only [inversePowerTwo_value] using
      representativeBandWithWork_value source target parent center b P tau (inversePowerTwo thetaExponent) child
  unfold unskippedCandidateWithWork testUnskippedBand
  dsimp only
  change _ = (if hband : band = [] then _ else _)
  by_cases hband : band = []
  · have hactual := hbandValue.trans hband
    simp only [dite_eq_left hactual, dite_eq_left hband]
  · have hactual : (representativeBandWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo thetaExponent) child).1 ≠ [] := fun h => hband (hbandValue.symm.trans h)
    simp only [dite_eq_right hactual, dite_eq_right hband]
    have hround := rounded_band_congr thetaExponent b hbandValue hactual hband
      (fun j q => (initial j q).value)
    have hguard := unskippedGuardWithWork_value source target parent center b thetaExponent F
      (representativeBandWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo thetaExponent) child).1
      ((materializedWideActionsWithWork M parent center b P).1.map Vector.get) hactual initial hb
    conv_rhs at hguard =>
      rw [materializedWideActionsWithWork_value, hround]
      simp only [hbandValue]
    by_cases hs : (∑ i, bandChildEnvelope b band (fun j q => (initial j q).value) i) ≤ 64 * F.value * b
    · rw [dite_eq_left hs]
      by_cases hw : canonicalRoundedBandAction thetaExponent b band hband
          (fun j q => (initial j q).value) ∈ wideActionList M parent center b P
      · rw [dite_eq_left hw]
        by_cases hg : ∀ i, |rationalStateGap
            (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target
            (canonicalRoundedBandAction thetaExponent b band hband (fun j q => (initial j q).value) i)| ≤
              2 * bandChildEnvelope b band (fun j q => (initial j q).value) i
        · rw [dite_eq_left hg, dite_eq_left (hguard.mpr ⟨hs, hw, hg⟩)]
        · rw [dite_eq_right hg, dite_eq_right (fun h => hg (hguard.mp h).2.2)]
      · rw [dite_eq_right hw, dite_eq_right (fun h => hw (hguard.mp h).2.1)]
    · rw [dite_eq_right hs, dite_eq_right (fun h => hs (hguard.mp h).1)]

end BinaryFraction
end EditApproximation

end OAI
