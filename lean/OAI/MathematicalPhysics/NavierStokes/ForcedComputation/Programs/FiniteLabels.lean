import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteRecorder
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.GappedSeparation

namespace OAI

/-! Computable state and symbol labels obtained by indexing explicit finite lists. -/

namespace ForcedComputation.Recorder

def controlEnumeration (M : Alternating.Machine) : List (Control (State M) (Alphabet M)) :=
  (allControls M).dedup

def symbolEnumeration (M : Alternating.Machine) : List (Symbol (State M) (Alphabet M)) :=
  (allSymbols M).dedup

def controlLabel (M : Alternating.Machine) :
    Control (State M) (Alphabet M) ≃ Fin (controlEnumeration M).length :=
  (List.Nodup.getEquivOfForallMemList (controlEnumeration M) (List.nodup_dedup _)
    (fun q => by simpa [controlEnumeration] using mem_allControls M q)).symm

def symbolLabel (M : Alternating.Machine) :
    Symbol (State M) (Alphabet M) ≃ Fin (symbolEnumeration M).length :=
  (List.Nodup.getEquivOfForallMemList (symbolEnumeration M) (List.nodup_dedup _)
    (fun a => by simpa [symbolEnumeration] using mem_allSymbols M a)).symm

def radixBase (M : Alternating.Machine) : ℚ :=
  Radix.rationalBase (symbolEnumeration M).length

def radixDigit (M : Alternating.Machine) (a : Symbol (State M) (Alphabet M)) : ℚ :=
  Radix.rationalDigit (symbolLabel M a)

theorem radixBase_gt_one (M : Alternating.Machine) : (1 : ℚ) < radixBase M := by
  dsimp [radixBase, Radix.rationalBase]
  have hn : (0 : ℚ) ≤ (symbolEnumeration M).length := by positivity
  linarith

theorem radixDigit_bounds (M : Alternating.Machine) (a : Symbol (State M) (Alphabet M)) :
    0 ≤ (radixDigit M a : ℝ) ∧ (radixDigit M a : ℝ) + 1 ≤ (radixBase M : ℝ) :=
  Radix.rationalDigit_bounds (symbolLabel M a)

theorem radixDigit_gap (M : Alternating.Machine) {a b : Symbol (State M) (Alphabet M)}
    (hab : a ≠ b) : 2 ≤ |(radixDigit M a : ℝ) - (radixDigit M b : ℝ)| :=
  Radix.rationalDigit_gap (fun h => hab ((symbolLabel M).injective h))

def bandScale (M : Alternating.Machine) : ℚ :=
  1 / (64 * ((controlEnumeration M).length + 1))

def centerY (M : Alternating.Machine) (q : Control (State M) (Alphabet M)) : ℚ :=
  3 / 8 + ((controlLabel M q).val + 1) / (16 * ((controlEnumeration M).length + 1))

def recorderHalting (M : Alternating.Machine) (q : Control (State M) (Alphabet M)) : Bool :=
  Control.casesOn q (fun q => M.isHalting q.val)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)

def stateOffset (M : Alternating.Machine) (q : Control (State M) (Alphabet M)) : Fin 2 → ℚ :=
  ![(if recorderHalting M q then 3 / 4 else 1 / 4) - bandScale M / 2,
    centerY M q - bandScale M / 2]

theorem bandScale_pos (M : Alternating.Machine) : 0 < bandScale M := by
  dsimp [bandScale]
  positivity

theorem bandScale_le (M : Alternating.Machine) : bandScale M ≤ 1 / 64 := by
  dsimp [bandScale]
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  have hn : (0 : ℚ) ≤ (controlEnumeration M).length := by positivity
  nlinarith

theorem centerY_bounds (M : Alternating.Machine) (q : Control (State M) (Alphabet M)) :
    3 / 8 < centerY M q ∧ centerY M q < 7 / 16 := by
  have hi : ((controlLabel M q).val : ℚ) < (controlEnumeration M).length := by
    exact_mod_cast (controlLabel M q).isLt
  have hi0 : (0 : ℚ) ≤ (controlLabel M q).val := by positivity
  have hd : (0 : ℚ) < 16 * ((controlEnumeration M).length + 1) := by positivity
  dsimp [centerY]
  constructor
  · have hp : 0 < (((controlLabel M q).val : ℚ) + 1) /
        (16 * ((controlEnumeration M).length + 1)) := div_pos (by linarith) hd
    linarith
  · have hp : (((controlLabel M q).val : ℚ) + 1) /
        (16 * ((controlEnumeration M).length + 1)) < 1 / 16 := by
      apply (div_lt_div_iff₀ hd (by norm_num)).mpr
      nlinarith
    linarith

theorem centerY_gap (M : Alternating.Machine)
    {q r : Control (State M) (Alphabet M)} (hqr : q ≠ r) :
    4 * (bandScale M : ℝ) ≤ |(centerY M q : ℝ) - (centerY M r : ℝ)| := by
  have hne : (controlLabel M q).val ≠ (controlLabel M r).val := by
    intro h
    exact hqr ((controlLabel M).injective (Fin.ext h))
  have hg : (1 : ℝ) ≤ |((controlLabel M q).val : ℝ) - (controlLabel M r).val| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : ((controlLabel M q).val : ℝ) + 1 ≤ (controlLabel M r).val := by
        exact_mod_cast (Nat.succ_le_iff.mpr h)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : ((controlLabel M r).val : ℝ) + 1 ≤ (controlLabel M q).val := by
        exact_mod_cast (Nat.succ_le_iff.mpr h)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hd : (0 : ℝ) < 16 * ((controlEnumeration M).length + 1) := by positivity
  have he : (centerY M q : ℝ) - (centerY M r : ℝ) =
      (((controlLabel M q).val : ℝ) - (controlLabel M r).val) /
        (16 * ((controlEnumeration M).length + 1)) := by
    simp only [centerY, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_ofNat]
    ring
  rw [he, abs_div, abs_of_pos hd]
  apply (le_div_iff₀ hd).mpr
  have hs : 4 * (bandScale M : ℝ) * (16 * ((controlEnumeration M).length + 1)) = 1 := by
    simp only [bandScale, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, Rat.cast_ofNat]
    field_simp
    ring
  simpa only [hs] using hg

end ForcedComputation.Recorder

end OAI
