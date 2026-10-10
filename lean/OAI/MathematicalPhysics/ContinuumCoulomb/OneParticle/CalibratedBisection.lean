import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedEvaluationComponents
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombTargetLipschitz
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.BisectionProgram

namespace OAI

/-! Deterministic bisection with the concrete hopping/Coulomb evaluator.
The premises are endpoint signs and the already proved separated-site gap;
there is no numeric evaluator assumption. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

abbrev BisectionInput := ℕ × (Environment × (ℚ × ℚ))

def bisectionInputCode : BisectionInput → List Bool :=
  prodCode unaryCode (prodCode environmentCode (prodCode ratCode ratCode))

def tolerance (e : Environment) : ℚ := 1 / ((e.1.2 : ℚ) + 1)

def bisectionArgument (x : BisectionInput) : BisectionProgram.Input Environment :=
  (x.1, (x.2.1, (tolerance x.2.1, x.2.2)))

def bisect (rho : ℕ) (x : BisectionInput) : ℚ :=
  BisectionProgram.approximate (value rho) (bisectionArgument x)

noncomputable opaque bisectionArgumentProgram : Procedure bisectionInputCode
    (BisectionProgram.inputCode environmentCode) bisectionArgument := by
  let n := Procedure.first unaryCode (prodCode environmentCode (prodCode ratCode ratCode))
  let tail := Procedure.second unaryCode (prodCode environmentCode (prodCode ratCode ratCode))
  let env := (Procedure.first environmentCode (prodCode ratCode ratCode)).comp tail
  let ends := (Procedure.second environmentCode (prodCode ratCode ratCode)).comp tail
  let np := (Procedure.first (prodCode unaryCode unaryCode)
    (prodCode unaryCode (prodCode ratCode ratCode))).comp env
  let p := (Procedure.second unaryCode unaryCode).comp np
  let p1 := Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (Procedure.unarySuccessor.comp p))
  let delta := Procedure.ratInv.comp p1
  exact (n.pair (env.pair (delta.pair ends))).congrFun (by
    intro x
    simp only [Function.comp_apply, id_eq, Nat.succ_eq_add_one, bisectionArgument,
      tolerance, one_div, Nat.cast_add, Nat.cast_one]
    )

def residual (rho : ℕ) (e : Environment) (d : ℝ) : ℝ :=
  (e.2.1 : ℝ) * planarHopping d -
    coulombHoppingTarget (GaussianFrequency.frequency rho) e.2.2.1 e.2.2.2 d

def residualLipschitz (rho : ℕ) (e : Environment) : ℝ :=
  (e.2.1 : ℝ) * planarHoppingLipschitzConstant +
    coulombTargetLipschitzConstant (GaussianFrequency.frequency rho) e.2.2.1 e.2.2.2

theorem bisect_residual (rho : ℕ) (hrho : 0 < rho) (e : Environment) (a b : ℚ)
    (hK : 0 ≤ e.2.2.2) (hKN : (e.2.2.2 : ℝ) ≤ e.1.1)
    (hτ : 0 ≤ e.2.2.1) (hτ1 : e.2.2.1 ≤ 1) (hab : a ≤ b)
    (haN : -(e.1.1 : ℝ) ≤ a) (hbN : (b : ℝ) ≤ e.1.1)
    (ha : 0 ≤ residual rho e a) (hb : residual rho e b ≤ 0)
    (hgap : ∀ r ∈ Set.Icc (a : ℝ) b,
      localizedGramConstant (GaussianFrequency.frequency rho) ≤
        localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
          localizedCoulombProfile (GaussianFrequency.frequency rho) r) (n : ℕ) :
    |residual rho e (bisect rho (n, (e, (a, b))))| ≤
      2 * ((e.1.2 : ℝ) + 1)⁻¹ +
        residualLipschitz rho e * (((b : ℝ) - a) / 2 ^ n) := by
  have hf : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have hKr : (0 : ℝ) ≤ e.2.2.2 := by exact_mod_cast hK
  have hτr : (0 : ℝ) ≤ e.2.2.1 := by exact_mod_cast hτ
  have hLip0 : 0 ≤ residualLipschitz rho e := add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (coulombTargetLipschitzConstant_nonnegative _ _ hτr)
  have heval (q : ℚ) (hq : q ∈ Set.Icc a b) :
      |(value rho e q : ℝ) - residual rho e q| ≤ (tolerance e : ℝ) := by
    have hqa : (a : ℝ) ≤ q := by exact_mod_cast hq.1
    have hqb : (q : ℝ) ≤ b := by exact_mod_cast hq.2
    have hqN : |(q : ℝ)| ≤ e.1.1 := abs_le.mpr ⟨haN.trans hqa, hqb.trans hbN⟩
    have hg := (localizedGramConstant_positive hf).le.trans (hgap q ⟨hqa, hqb⟩)
    have he := approximation_error rho hrho e q hK hKN hτ hτ1 hqN hg
    simpa only [residual, coulombHoppingTarget, tolerance, Rat.cast_div,
      Rat.cast_one, Rat.cast_add, Rat.cast_natCast, one_div, Rat.cast_inv] using he
  have hLip (r : ℝ) (hr : r ∈ Set.Icc (a : ℝ) b)
      (s : ℝ) (hs : s ∈ Set.Icc (a : ℝ) b) :
      |residual rho e r - residual rho e s| ≤ residualLipschitz rho e * |r - s| :=
    calibratedResidual_abs_sub hf hτr hKr (Nat.cast_nonneg _) r s (hgap r hr) (hgap s hs)
  have ht : 0 ≤ tolerance e := by unfold tolerance; positivity
  have h := BisectionProgram.residual (value rho) e ht hab ha hb hLip0 heval hLip n
  simpa only [bisect, bisectionArgument, tolerance, Rat.cast_div, Rat.cast_one,
    Rat.cast_add, Rat.cast_natCast, one_div, Rat.cast_inv] using h

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
