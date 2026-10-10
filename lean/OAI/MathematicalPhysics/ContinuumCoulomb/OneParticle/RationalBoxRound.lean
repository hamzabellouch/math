import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalSumProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserVelocityNumerics
import OAI.Computability.QuantumFactoring.BitStackRationalFloor

namespace OAI

/-! Bounded integer numerator registers for rounded Euler iteration.
Clipping to a fixed box prevents malformed evaluator outputs from causing
unbounded register growth. On valid trajectories clipping never increases
the distance to the exact coordinate. -/

namespace ContinuumCoulomb.RationalBoxRound
open ExactQuantumFactoring.BitStackProgram

def clip (B : ℕ) (z : ℤ) : ℤ := max (-(B:ℤ)) (min (B:ℤ) z)

theorem clip_bounds (B : ℕ) (z : ℤ) : -(B:ℤ) ≤ clip B z ∧ clip B z ≤ B := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by omega) (min_le_left _ _)

theorem clip_natAbs (B : ℕ) (z : ℤ) : (clip B z).natAbs ≤ B := by
  have h := clip_bounds B z
  have ha : ((clip B z).natAbs:ℤ) ≤ (B:ℤ) := by
    simpa only [Int.natCast_natAbs] using (abs_le.mpr h : |clip B z| ≤ (B:ℤ))
  exact_mod_cast ha

def numerator (D B : ℕ) (q : ℚ) : ℤ := clip B ⌊(D:ℚ)*q⌋
def value (D B : ℕ) (q : ℚ) : ℚ := (numerator D B q:ℚ)/(D:ℚ)

theorem numerator_bits (D B : ℕ) (q : ℚ) :
    (numerator D B q).natAbs.bits.length ≤ B.bits.length :=
  bits_length_mono (clip_natAbs _ _)

theorem clip_real_error {B x q : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |max (-B) (min B q)-x| ≤ |q-x| := by
  by_cases hlo : q ≤ -B
  · rw [min_eq_right (by linarith),max_eq_left hlo]
    have hxl := (abs_le.mp hx).1
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  · by_cases hhi : B ≤ q
    · rw [min_eq_left hhi,max_eq_right (by linarith)]
      have hxu := (abs_le.mp hx).2
      rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
      linarith
    · rw [min_eq_right (le_of_not_ge hhi),max_eq_right (le_of_not_ge hlo)]

theorem value_error {D B : ℕ} (hD : 0 < D) (q : ℚ) (x : ℝ)
    (hx : |x| ≤ (B:ℝ)/(D:ℝ)) :
    |(value D B q:ℝ)-x| ≤ |(q:ℝ)-x|+1/(D:ℝ) := by
  have hDp : (0:ℝ) < D := by exact_mod_cast hD
  have hfloor : |(⌊(D:ℚ)*q⌋:ℝ)-(D:ℝ)*(q:ℝ)| ≤ 1 := by
    have hl := Int.floor_le ((D:ℚ)*q)
    have hu := Int.lt_floor_add_one ((D:ℚ)*q)
    have hlR : (⌊(D:ℚ)*q⌋:ℝ) ≤ (D:ℝ)*(q:ℝ) := by exact_mod_cast hl
    have huR : (D:ℝ)*(q:ℝ) < (⌊(D:ℚ)*q⌋:ℝ)+1 := by exact_mod_cast hu
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have htarget : |(D:ℝ)*x| ≤ B := by
    rw [abs_mul,abs_of_pos hDp]
    exact (mul_le_mul_of_nonneg_left hx hDp.le).trans_eq (by field_simp)
  have hc := clip_real_error (show (0:ℝ) ≤ B by positivity) htarget
    (q := (⌊(D:ℚ)*q⌋:ℝ))
  have hcast : (numerator D B q:ℝ) =
      max (-(B:ℝ)) (min (B:ℝ) (⌊(D:ℚ)*q⌋:ℝ)) := by
    simp only [numerator,clip,Int.cast_max,Int.cast_min,Int.cast_neg,Int.cast_natCast]
  rw [← hcast] at hc
  have ht := abs_sub_le (⌊(D:ℚ)*q⌋:ℝ) ((D:ℝ)*(q:ℝ)) ((D:ℝ)*x)
  have hscale : |(D:ℝ)*(q:ℝ)-(D:ℝ)*x| = (D:ℝ)*|(q:ℝ)-x| := by
    rw [← mul_sub,abs_mul,abs_of_pos hDp]
  rw [hscale] at ht
  have heq : (value D B q:ℝ)-x = ((numerator D B q:ℝ)-(D:ℝ)*x)/(D:ℝ) := by
    simp only [value,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
    field_simp
  rw [heq,abs_div,abs_of_pos hDp]
  apply (div_le_iff₀ hDp).mpr
  have hs : (|(q:ℝ)-x|+1/(D:ℝ))*(D:ℝ) = (D:ℝ)*|(q:ℝ)-x|+1 := by field_simp
  rw [hs]
  linarith

abbrev Input := (ℕ×ℕ)×ℚ
def inputCode : Input → List Bool := prodCode (prodCode Nat.bits Nat.bits) ratCode

noncomputable opaque clipProgram : Procedure (prodCode Nat.bits intCode) intCode
    (fun x => clip x.1 x.2) := by
  let B := Procedure.natToInt.comp (Procedure.first Nat.bits intCode)
  let z := Procedure.second Nat.bits intCode
  let low := Procedure.intNeg.comp B
  let tooLow := Procedure.intSign.comp (Procedure.intSub.comp (z.pair low))
  let tooHigh := Procedure.intSign.comp (Procedure.intSub.comp (B.pair z))
  exact (Procedure.conditional tooLow low (Procedure.conditional tooHigh B z)).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq]
    unfold clip
    split_ifs with hlo hhi
    · rw [min_eq_right (by linarith),max_eq_left (by linarith)]
    · rw [min_eq_left (by linarith),max_eq_right (by omega)]
    · rw [min_eq_right (by linarith),max_eq_right (by linarith)])

noncomputable opaque numeratorProgram : Procedure inputCode intCode
    (fun x => numerator x.1.1 x.1.2 x.2) := by
  let db := Procedure.first (prodCode Nat.bits Nat.bits) ratCode
  let d := (Procedure.first Nat.bits Nat.bits).comp db
  let b := (Procedure.second Nat.bits Nat.bits).comp db
  let q := Procedure.second (prodCode Nat.bits Nat.bits) ratCode
  let scaled := Procedure.ratMul.comp ((Procedure.natToRat.comp d).pair q)
  exact (clipProgram.comp (b.pair (Procedure.ratFloor.comp scaled))).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure inputCode ratCode
    (fun x => value x.1.1 x.1.2 x.2) := by
  let db := Procedure.first (prodCode Nat.bits Nat.bits) ratCode
  let d := (Procedure.first Nat.bits Nat.bits).comp db
  exact (Procedure.ratDiv.comp ((Procedure.intToRat.comp numeratorProgram).pair
    (Procedure.natToRat.comp d))).congrFun (by intro x; rfl)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode intCode
    (fun x => numerator x.1.1 x.1.2 x.2) := numeratorProgram.toTM2

end ContinuumCoulomb.RationalBoxRound

end OAI
