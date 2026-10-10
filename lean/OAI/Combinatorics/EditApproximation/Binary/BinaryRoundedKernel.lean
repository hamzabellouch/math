import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryMedianKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryGridWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryActualBandOptimizer
import OAI.Combinatorics.EditApproximation.Geometry.UnskippedBands
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Exact rounded canonical actions from their computed binary envelopes.
Rounding spacing is obtained by a natural ceiling, since the dyadic product
is either below one or an integer. No logarithm is evaluated. -/

namespace EditApproximation

open Finset

private theorem interval_eq_of_endpoints {n : ℕ} (a b : TargetInterval n)
    (hl : a.lo = b.lo) (hh : a.hi = b.hi) : a = b := by
  cases a
  cases b
  cases hl
  cases hh
  rfl

/-- A binary interval output, with its order/range proofs erased. -/


@[simp] theorem roundStateWithWork_value {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (q : TargetInterval n) : (roundStateWithWork spacing hspacing q).1 = roundInterval spacing q := by
  apply interval_eq_of_endpoints
  · exact congrArg Prod.fst (binaryIntervalRoundWithWork_value spacing hspacing q)
  · exact congrArg Prod.snd (binaryIntervalRoundWithWork_value spacing hspacing q)



@[simp] theorem actionEqualWithWork_value {n M : ℕ} (a b : Fin M → TargetInterval n) :
    (actionEqualWithWork a b).1 = true ↔ a = b := by
  simp only [actionEqualWithWork, allWithWork_value, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, naturalEqualWithWork_value]
  constructor
  · intro h
    funext i
    exact interval_eq_of_endpoints _ _ (h i).1 (h i).2
  · intro h
    subst b
    exact fun _ => ⟨rfl, rfl⟩

/-- A literal membership scan, preserving the wide-list definition on
inaccurate as well as accurate input seeds. -/


@[simp] theorem actionMemberWithWork_value {n M : ℕ} (a : Fin M → TargetInterval n)
    (actions : List (Fin M → TargetInterval n)) :
    (actionMemberWithWork a actions).1 = true ↔ a ∈ actions := by
  induction actions with
  | nil => simp only [actionMemberWithWork, Bool.false_eq_true, List.not_mem_nil]
  | cons b rest ih =>
    simp only [actionMemberWithWork, Bool.or_eq_true, actionEqualWithWork_value, ih, List.mem_cons]

namespace BinaryFraction



@[simp] theorem roundedSpacingWithWork_value (theta envelope : BinaryFraction) :
    bitWordValue (roundedSpacingWithWork theta envelope).1 = ⌈max 1 (theta.value * envelope.value)⌉₊ := by
  simp only [roundedSpacingWithWork, naturalCeilingWithWork_value, maxWithWork_value,
    canonicalMulWithWork_value, one, nat_value, Nat.cast_one]

theorem roundedSpacingWithWork_pos (theta envelope : BinaryFraction) :
    0 < bitWordValue (roundedSpacingWithWork theta envelope).1 := by
  rw [roundedSpacingWithWork_value, Nat.ceil_pos]
  exact lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (le_max_left _ _)

theorem roundedSpacingWithWork_band_value {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (i : Fin M) (hb : 0 < b) :
    bitWordValue (roundedSpacingWithWork (inversePowerTwo thetaExponent)
      (bandEnvelopeWithWork b band initial i).1).1 =
      bandRoundSpacing thetaExponent b band (fun j q => (initial j q).value) i := by
  rw [roundedSpacingWithWork_value, inversePowerTwo_value, bandEnvelopeWithWork_value _ _ _ _ hb,
    ← bandRoundSpacing_exact thetaExponent b band (fun j q => (initial j q).value) i, Nat.ceil_natCast]

def roundedBandWithWork {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval ny → BinaryFraction) :
    Vector (TargetInterval ny) M × ℕ :=
  vectorMapWithWork M fun i =>
    let envelope := bandEnvelopeWithWork b band initial i
    let spacing := roundedSpacingWithWork (inversePowerTwo thetaExponent) envelope.1
    let rounded := roundStateWithWork (bitWordValue spacing.1)
      (roundedSpacingWithWork_pos _ _) (band.head hne i)
    (rounded.1, envelope.2 + spacing.2 + rounded.2 + thetaExponent + 3)

@[simp] theorem roundedBandWithWork_value {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval ny → BinaryFraction) (hb : 0 < b) :
    (roundedBandWithWork thetaExponent b band hne initial).1.get =
      canonicalRoundedBandAction thetaExponent b band hne (fun j q => (initial j q).value) := by
  funext i
  simp only [roundedBandWithWork, vectorMapWithWork_value, roundStateWithWork_value,
    roundedSpacingWithWork_band_value _ _ _ _ _ hb,
    canonicalRoundedBandAction, roundedBandAction]

/-- All numerical acceptance tests after a nonempty band has been built. -/
def unskippedGuardWithWork {nx ny M : ℕ} (parent : TargetInterval nx) (_center : TargetInterval ny)
    (b thetaExponent : ℕ) (F : BinaryFraction) (band wide : List (Fin M → TargetInterval ny))
    (hne : band ≠ []) (initial : Fin M → TargetInterval ny → BinaryFraction) : Bool × ℕ :=
  let envelope := envelopeVectorWithWork b band initial
  let total := bandMassTotalWithWork envelope.1
  let fb := canonicalMulWithWork F (nat b)
  let limit := canonicalMulWithWork (nat 64) fb.1
  let sumGuard := leWithWork total.1 limit.1
  let rounded := roundedBandWithWork thetaExponent b band hne initial
  let wideGuard := actionMemberWithWork rounded.1.get wide
  let gapGuard := allWithWork (fun i =>
    let sourceLength := binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo
    let gap := stateGapWithWork (bitWordValue sourceLength.1) (rounded.1.get i)
    let bound := canonicalMulWithWork (nat 2) (envelope.1.get i)
    let test := leWithWork gap.1.absolute bound.1
    (test.1, sourceLength.2 + gap.2 + bound.2 + test.2 + 3)) (List.finRange M)
  (sumGuard.1 && wideGuard.1 && gapGuard.1,
    envelope.2 + total.2 + fb.2 + limit.2 + sumGuard.2 + rounded.2 + wideGuard.2 + gapGuard.2 + 5)

@[simp] theorem unskippedGuardWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (center : TargetInterval target.length)
    (b thetaExponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval target.length)) (hne : band ≠ [])
    (initial : Fin M → TargetInterval target.length → BinaryFraction) (hb : 0 < b) :
    (unskippedGuardWithWork parent center b thetaExponent F band wide hne initial).1 = true ↔
      (∑ i, bandChildEnvelope b band (fun j q => (initial j q).value) i) ≤ 64 * F.value * b ∧
      canonicalRoundedBandAction thetaExponent b band hne (fun j q => (initial j q).value) ∈ wide ∧
      ∀ i, |rationalStateGap
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target
        (canonicalRoundedBandAction thetaExponent b band hne (fun j q => (initial j q).value) i)| ≤
          2 * bandChildEnvelope b band (fun j q => (initial j q).value) i := by
  have hsub (i : Fin M) :
      bitWordValue (binaryNaturalSubtractWithWork (sourceChild parent i).hi (sourceChild parent i).lo).1 =
        (sourceChild parent i).hi - (sourceChild parent i).lo :=
    binaryNaturalSubtractWithWork_value _ _ (sourceChild parent i).ordered
  simp only [unskippedGuardWithWork, Bool.and_eq_true, leWithWork_value,
    bandMassTotalWithWork_value, canonicalMulWithWork_value, nat_value,
    envelopeVectorWithWork_value b band initial hb, roundedBandWithWork_value _ _ _ _ _ hb,
    actionMemberWithWork_value, allWithWork_value, List.mem_finRange, forall_true_left,
    absolute_value, stateGapWithWork_value, hsub, rationalStateGap,
    substring_length source _ _ (sourceChild parent _).valid]
  rw [mul_assoc, Nat.cast_ofNat, and_assoc, Nat.cast_ofNat]

end BinaryFraction
end EditApproximation

end OAI
