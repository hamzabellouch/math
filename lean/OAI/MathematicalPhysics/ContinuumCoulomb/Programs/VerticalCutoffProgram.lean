import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SmoothTransitionProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedWellField

namespace OAI

/-! Polynomial-time approximation of the actual transverse cutoff in the
manufactured well field. The rational slab width and coordinate are arbitrary. -/

namespace ContinuumCoulomb.VerticalCutoffProgram
open ExactQuantumFactoring.BitStackProgram

theorem cutoff_error (p : ℕ) (q : ℚ) :
    |(SmoothTransitionProgram.cutoff p q:ℝ)-verticalCutoffBump (q:ℝ)| ≤
      ((p:ℝ)+1)⁻¹ := by
  simpa only [SmoothTransitionProgram.cutoff,SmoothTransitionProgram.cutoffArgument,
    verticalCutoffBump,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat]
    using RationalSmoothTransition.approximation_error p (SmoothTransitionProgram.cutoffArgument q)

abbrev Input := ℕ × (ℚ × ℚ)
def inputCode : Input → List Bool := prodCode unaryCode (prodCode ratCode ratCode)
def argument (x : Input) : ℚ := 2/x.2.1*x.2.2
def value (x : Input) : ℚ := SmoothTransitionProgram.cutoff x.1 (argument x)

noncomputable opaque argumentProgram : Procedure inputCode ratCode argument := by
  let rest := Procedure.second unaryCode (prodCode ratCode ratCode)
  let S := (Procedure.first ratCode ratCode).comp rest
  let z := (Procedure.second ratCode ratCode).comp rest
  let two := Procedure.constant inputCode ratCode (2:ℚ)
  exact (Procedure.ratMul.comp ((Procedure.ratDiv.comp (two.pair S)).pair z)).congrFun
    (by intro x; rfl)

noncomputable opaque program : Procedure inputCode ratCode value :=
  (SmoothTransitionProgram.cutoffProgram.comp
    ((Procedure.first unaryCode (prodCode ratCode ratCode)).pair argumentProgram)).congrFun
    (by intro x; rfl)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode ratCode value := program.toTM2

theorem approximation_error (x : Input) :
    |(value x:ℝ)-slabWellCutoff (x.2.1:ℝ) (x.2.2:ℝ)| ≤ ((x.1:ℝ)+1)⁻¹ := by
  simpa only [value,argument,slabWellCutoff,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
    using cutoff_error x.1 (argument x)

end ContinuumCoulomb.VerticalCutoffProgram

end OAI
