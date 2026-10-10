import OAI.Combinatorics.EditApproximation.Binary.BinaryCoordinateActionWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryPowerStorage
import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The online branch computes its representative, all guards, coordinate
count, iteration bound and accepted source residue before executing the
literal finite optimizer. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem reduceOnlineIntegerWithWork_value (K : ℕ) (hK : 0 < K) (integer : ℕ) :
    (reduceOnlineIntegerWithWork K hK integer).1 =
      boundedOnlineInteger (optimizerTriangularMass K) (optimizerTriangularMass_positive K hK) integer := by
  apply Fin.ext
  change bitWordValue (binaryNaturalDivModWithWork integer
    (bitWordValue (triangularMassWithWork K).1)).2.1 = integer % optimizerTriangularMass K
  rw [triangularMassWithWork_value]
  exact (binaryNaturalDivModWithWork_spec integer _ (optimizerTriangularMass_positive K hK)).2



@[simp] theorem onlineIndexSetupWithWork_value {M n : ℕ} (H : ℕ)
    (band : List (Fin M → TargetInterval n)) :
    (onlineIndexSetupWithWork H band).1 = H + (listedBandCoordinates band).length + 2 := by
  simp only [onlineIndexSetupWithWork, binaryNaturalAddWithWork_value, bandCoordinatesWithWork_value]

private def onlineBandReference {M n : ℕ} (center : TargetInterval n) (b G : ℕ) (hG : 0 < G)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ []) (t integer : ℕ) :
    PhysicalRationalAction M n :=
  sharedBandRationalAction center
    (finiteOptimizerActionDraw band hne (bandChildEnvelope b band (fun i q => (initial i q).value))
      (rationalOnlineLinear eta.value kappa.value
        (childGain (bandChildEnvelope b band (fun i q => (initial i q).value))
          (fun s coordinate => (table s coordinate).value))
        (childDecrement (bandChildEnvelope b band (fun i q => (initial i q).value))
          (fun s coordinate => (table s coordinate).value)) t)
      G (G ^ 80) (boundedOnlineInteger _ (optimizerTriangularMass_positive _ (pow_pos hG _)) integer))

private theorem onlineBandReference_congr {M n : ℕ} (center : TargetInterval n)
    (b G G' : ℕ) (hG : 0 < G) (hG' : 0 < G') (heq : G = G')
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band band' : List (Fin M → TargetInterval n)) (hband : band = band')
    (hne : band ≠ []) (hne' : band' ≠ []) (t integer : ℕ) :
    onlineBandReference center b G hG initial table eta kappa band hne t integer =
      onlineBandReference center b G' hG' initial table eta kappa band' hne' t integer := by
  cases heq
  cases hband
  rfl

def keyedOnlineWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let band := representativeBandWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child
  let setup := onlineIndexSetupWithWork H band.1
  let G := setup.1
  let accepted := reduceOnlineIntegerWithWork (G ^ 80) (by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  if hband : band.1 = [] then (none, band.2 + setup.2 + accepted.2 + 1) else
    let guard := unskippedCandidateWithWork source target parent b P exponent hb tau (nat F) child initial center
    if guard.1.isSome then
      let sampled := countedSampledOnlineWithWork center b initial table eta kappa band.1 hband
        G (G ^ 80) t accepted.1
      (some sampled.1, band.2 + setup.2 + accepted.2 + guard.2 + sampled.2 + 2)
    else (none, band.2 + setup.2 + accepted.2 + guard.2 + 1)

theorem keyedOnlineWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ) :
    ((keyedOnlineWithWork source target parent P F exponent H b hb tau eta kappa child initial table
      t center integer).1.map BinaryBellmanAction.decode) =
      keyedOnlineCandidate source target parent P F exponent H b tau.value eta.value kappa.value
        (fun i q => (child i q).value) (fun i q => (initial i q).value)
        (fun i s q => (table s (i, q)).value) t center integer := by
  have hband := representativeBandWithWork_value source target parent center b P tau (inversePowerTwo exponent) child
  simp only [inversePowerTwo_value] at hband
  have hG : (onlineIndexSetupWithWork H (representativeBandWithWork parent center
      (parent.hi - parent.lo) b P tau (inversePowerTwo exponent) child).1).1 =
      keyedOnlineBandG source target parent P exponent H b tau.value (fun i q => (child i q).value) center := by
    rw [onlineIndexSetupWithWork_value, listedBandCoordinates_length, hband]
    rfl
  have hGpos : 0 < (onlineIndexSetupWithWork H (representativeBandWithWork parent center
      (parent.hi - parent.lo) b P tau (inversePowerTwo exponent) child).1).1 := by
    rw [onlineIndexSetupWithWork_value]
    omega
  have hGpos' : 0 < keyedOnlineBandG source target parent P exponent H b tau.value
      (fun i q => (child i q).value) center := by
    rw [← hG]
    exact hGpos
  have htest := unskippedCandidateWithWork_value source target parent b P exponent hb tau (nat F) child initial center
  unfold keyedOnlineWithWork
  dsimp only
  split_ifs with hempty hactive
  · have he : representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (child i q).value) = [] := hband.symm.trans hempty
    simp only [Option.map_none, keyedOnlineCandidate, dite_eq_left he]
  · have he : representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (child i q).value) ≠ [] :=
      fun hz => hempty (hband.trans hz)
    rw [htest] at hactive
    rw [congrArg (fun f : ℚ => (testUnskippedBand source target parent b P exponent tau.value f
      (fun i q => (child i q).value) (fun i q => (initial i q).value) center).isSome) (nat_value F)] at hactive
    unfold keyedOnlineCandidate
    simp only [dite_eq_right he]
    cases ht : testUnskippedBand source target parent b P exponent tau.value (F : ℚ)
        (fun i q => (child i q).value) (fun i q => (initial i q).value) center with
    | none =>
      have hf : (none : Option (UnskippedBand source target parent b P exponent tau.value (F : ℚ)
        (fun i q => (child i q).value) (fun i q => (initial i q).value))).isSome = true := by
        simpa only [← ht] using hactive
      cases hf
    | some member =>
      simp only [Option.map_some, countedSampledOnlineWithWork_value,
        sampledOnlineActionWithWork_value _ _ _ _ _ _ _ _ _ _ _ _ hb,
        reduceOnlineIntegerWithWork_value]
      apply congrArg some
      exact onlineBandReference_congr center b _ _ hGpos hGpos' hG initial table eta kappa _ _ hband hempty he t integer
  · have he : representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (child i q).value) ≠ [] :=
      fun hz => hempty (hband.trans hz)
    rw [htest] at hactive
    rw [congrArg (fun f : ℚ => (testUnskippedBand source target parent b P exponent tau.value f
      (fun i q => (child i q).value) (fun i q => (initial i q).value) center).isSome) (nat_value F)] at hactive
    unfold keyedOnlineCandidate
    simp only [dite_eq_right he, Option.map_none]
    cases ht : testUnskippedBand source target parent b P exponent tau.value (F : ℚ)
        (fun i q => (child i q).value) (fun i q => (initial i q).value) center with
    | none => rfl
    | some member =>
      apply False.elim
      apply hactive
      rw [ht]
      rfl

end BinaryFraction
end EditApproximation

end OAI
