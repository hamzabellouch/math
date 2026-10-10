import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # The difference formula for matrix exponentials

The scalar-time exponential derivative and the fundamental theorem of
calculus give the noncommutative difference formula. This is the concrete
step toward identifying the differential in the retained Dixmier input.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

theorem hasDerivAt_exponential_bridge (a b : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((1 - s) • a) * NormedSpace.exp (s • b))
      (NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b)) t := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have ha := (hasDerivAt_exp_smul_const a (1 - t)).scomp t
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have hb := hasDerivAt_exp_smul_const b t
  have h := ha.mul hb
  have hc : Commute b (NormedSpace.exp (t • b)) :=
    ((Commute.refl b).smul_right t).exp_right
  have he : (-1 : ℝ) • (NormedSpace.exp ((1 - t) • a) * a) * NormedSpace.exp (t • b) +
      NormedSpace.exp ((1 - t) • a) * (NormedSpace.exp (t • b) * b) =
      NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b) := by
    rw [neg_one_smul, ← hc.eq]
    noncomm_ring
  change HasDerivAt (fun s : ℝ => NormedSpace.exp ((1 - s) • a) *
    NormedSpace.exp (s • b)) _ t at h
  simpa only [Function.comp_def, zero_sub, he] using h

theorem exponential_sub_eq_integral (a b : A) :
    NormedSpace.exp b - NormedSpace.exp a =
      ∫ t in (0 : ℝ)..1,
        NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b) := by
  have hc : Continuous (fun t : ℝ =>
      NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b)) :=
    ((NormedSpace.exp_continuous.comp ((continuous_const.sub continuous_id).smul
      continuous_const)).mul continuous_const).mul
        (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hasDerivAt_exponential_bridge a b t)
    (hc.intervalIntegrable (μ := volume) 0 1)
  simpa only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, sub_zero,
    one_smul, mul_one] using h.symm

end PolycyclicRecognition

end

end OAI
