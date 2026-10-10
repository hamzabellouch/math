import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorListProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ChargePrograms

namespace OAI

/-! Exact common-denominator source coefficient rounding, implemented by
actual integer/rational machine arithmetic. Nonzero rounded weights have
an inverse-polynomial lower bound without assuming one for the source. -/

namespace ContinuumCoulomb.SourceCoefficientRounding
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def coefficient (M : ℕ) (q : ℚ) : ℚ := (round ((M : ℚ) * q) : ℚ) / M

theorem coefficient_error {M : ℕ} (hM : 0 < M) (q : ℚ) :
    |q - coefficient M q| ≤ 1 / (2 * (M : ℚ)) := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have heq : q - coefficient M q = ((M : ℚ) * q - round ((M : ℚ) * q)) / M := by
    unfold coefficient
    field_simp
  rw [heq, abs_div, abs_of_pos hm]
  calc
    _ ≤ (1 / 2 : ℚ) / M := div_le_div_of_nonneg_right (abs_sub_round ((M : ℚ) * q)) hm.le
    _ = _ := by ring

theorem coefficient_nonzero_lower {M : ℕ} (hM : 0 < M) (q : ℚ)
    (hq : coefficient M q ≠ 0) : 1 / (M : ℚ) ≤ |coefficient M q| := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have hk : round ((M : ℚ) * q) ≠ 0 := by
    intro hk
    apply hq
    simp only [coefficient, hk, Int.cast_zero, zero_div]
  have ha : (1 : ℤ) ≤ |round ((M : ℚ) * q)| := by
    have hp := abs_nonneg (round ((M : ℚ) * q))
    have hn := abs_ne_zero.mpr hk
    omega
  have ha' : (1 : ℚ) ≤ |(round ((M : ℚ) * q) : ℚ)| := by exact_mod_cast ha
  rw [coefficient, abs_div, abs_of_pos hm]
  exact div_le_div_of_nonneg_right ha' hm.le

theorem coefficient_upper {M W : ℕ} (hM : 0 < M) (q : ℚ) (hq : |q| ≤ W) :
    |coefficient M q| ≤ W + 1 := by
  have hm : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have he := coefficient_error hM q
  have hhalf : (1 : ℚ) / (2 * M) ≤ 1 := by apply (div_le_one (by positivity)).mpr; linarith
  have h := abs_add_le (coefficient M q - q) q
  rw [sub_add_cancel] at h
  rw [abs_sub_comm] at he
  linarith

abbrev Input := ℕ × Bond

def inputCode : Input → List Bool := prodCode unaryCode bondCode

noncomputable def mProgram : Procedure inputCode ratCode (fun x => (x.1 : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp (Procedure.first _ _))
noncomputable def weightProgram : Procedure inputCode ratCode (fun x => x.2.2.2) :=
  ((Procedure.second _ _).comp (Procedure.second _ _)).comp (Procedure.second _ _)
noncomputable def roundedProgram : Procedure inputCode intCode
    (fun x => round ((x.1 : ℚ) * x.2.2.2)) :=
  ChargePrograms.rationalRoundProgram.comp (Procedure.ratMul.comp (mProgram.pair weightProgram))
noncomputable def coefficientProgram : Procedure inputCode ratCode
    (fun x => coefficient x.1 x.2.2.2) :=
  Procedure.ratDiv.comp ((Procedure.intToRat.comp roundedProgram).pair mProgram)

noncomputable def bondProgram : Procedure inputCode bondCode
    (fun x => (x.2.1, x.2.2.1, coefficient x.1 x.2.2.2)) := by
  let bond := Procedure.second unaryCode bondCode
  let left := (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp bond
  let right := ((Procedure.first Nat.bits ratCode).comp (Procedure.second Nat.bits _)).comp bond
  exact left.pair (right.pair coefficientProgram)

noncomputable def listProgram : Procedure (prodCode unaryCode (listCode bondCode))
    (listCode bondCode) (fun x => x.2.map (fun e => (e.1, e.2.1, coefficient x.1 e.2.2))) :=
  Procedure.listMapWith (ea := unaryCode) (eb := bondCode) (ec := bondCode)
    (f := fun (M : ℕ) (e : Bond) => (e.1, e.2.1, coefficient M e.2.2))
    zeroBond zeroBond bondProgram

end ContinuumCoulomb.SourceCoefficientRounding

end OAI
