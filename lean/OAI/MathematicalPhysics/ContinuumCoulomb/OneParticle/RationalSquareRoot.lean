import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.DyadicRootProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ChargePrograms

namespace OAI

/-! Certified evaluation of square roots of nonnegative rational samples.
The same finite dyadic procedure serves the fixed Gaussian constants and
softened Coulomb distances. -/

namespace ContinuumCoulomb.RationalSquareRoot
open ExactQuantumFactoring.BitStackProgram

def value (x : ℕ × ℚ) : ℚ :=
  DyadicRootProgram.value x.1 x.2.num.toNat x.2.den

def inputCode : (ℕ × ℚ) → List Bool := prodCode unaryCode ratCode

noncomputable opaque argumentProgram : Procedure inputCode DyadicRootProgram.rawCode
    (fun x => (x.1, x.2.num.toNat, x.2.den)) := by
  let p := Procedure.first unaryCode ratCode
  let q := Procedure.second unaryCode ratCode
  let num := ChargePrograms.intToNatProgram.comp (Procedure.ratNum.comp q)
  let den := Procedure.ratDen.comp q
  exact p.pair (num.pair den)

noncomputable opaque program : Procedure inputCode ratCode value :=
  (DyadicRootProgram.rawProgram.comp argumentProgram).congrFun (by intro x; rfl)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode ratCode value :=
  program.toTM2

theorem value_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    |(value (b, q) : ℝ) - Real.sqrt (q : ℝ)| ≤ (2 : ℝ)⁻¹ ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  have h := DyadicRootProgram.value_error b q.num.toNat q.den q.pos
  rw [hre] at h
  change |(DyadicRootProgram.value b q.num.toNat q.den : ℝ) - Real.sqrt (q : ℝ)| ≤ _
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2.le.trans_eq (by simp only [one_div, inv_pow])

theorem sqrt_perturbation {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  apply Real.abs_le_sqrt
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  by_cases hab : a ≤ b
  · have hs := Real.sqrt_le_sqrt hab
    have hm := mul_nonneg (Real.sqrt_nonneg a) (sub_nonneg.mpr hs)
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith
  · have hs := Real.sqrt_le_sqrt (le_of_not_ge hab)
    have hm := mul_nonneg (Real.sqrt_nonneg b) (sub_nonneg.mpr hs)
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
    nlinarith

end ContinuumCoulomb.RationalSquareRoot

end OAI
