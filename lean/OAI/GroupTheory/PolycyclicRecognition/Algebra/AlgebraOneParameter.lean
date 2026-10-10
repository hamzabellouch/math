import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Differentiable one-parameter subgroups in a real Banach algebra

The derivative at zero determines the curve. Multiplication by the inverse
exponential produces a function with zero derivative everywhere.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem oneParameter_hasDerivAt {f : ℝ → A} {v : A}
    (hadd : ∀ s t, f (s + t) = f s * f t) (hzero : HasDerivAt f v 0) (t : ℝ) :
    HasDerivAt f (v * f t) t := by
  have hbase : HasDerivAt (fun s => f s * f t) (v * f t) (t - t) := by
    rw [sub_self]
    exact hzero.mul_const (f t)
  have h := hbase.scomp (h := fun s : ℝ => s - t) t
    ((hasDerivAt_id t).sub_const t)
  have heq : (fun s : ℝ => f (s - t) * f t) = f := by
    funext s
    rw [← hadd, sub_add_cancel]
  change HasDerivAt (fun s : ℝ => f (s - t) * f t) _ t at h
  rw [heq] at h
  simpa only [sub_self, one_smul, mul_one] using h

theorem oneParameter_eq_exp {f : ℝ → A} {v : A}
    (hf0 : f 0 = 1) (hadd : ∀ s t, f (s + t) = f s * f t)
    (hzero : HasDerivAt f v 0) (t : ℝ) : f t = NormedSpace.exp (t • v) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let u : ℝ → A := fun s => NormedSpace.exp (s • (-v)) * f s
  have hu (s : ℝ) : HasDerivAt u 0 s := by
    have h := (hasDerivAt_exp_smul_const (-v) s).mul (oneParameter_hasDerivAt hadd hzero s)
    change HasDerivAt u _ s at h
    simpa only [mul_neg, neg_mul, mul_assoc, neg_add_cancel] using h
  have ht := is_const_of_deriv_eq_zero (fun s => (hu s).differentiableAt)
    (fun s => (hu s).deriv) t 0
  have hu0 : u 0 = 1 := by simp only [u, zero_smul, NormedSpace.exp_zero, one_mul, hf0]
  rw [hu0] at ht
  have hk : NormedSpace.exp (t • v) * NormedSpace.exp (t • (-v)) = 1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (t • v)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have hm := congrArg (fun z : A => NormedSpace.exp (t • v) * z) ht
  change NormedSpace.exp (t • v) * (NormedSpace.exp (t • (-v)) * f t) =
    NormedSpace.exp (t • v) * 1 at hm
  rw [← mul_assoc, hk, one_mul, mul_one] at hm
  exact hm

end PolycyclicRecognition

end

end OAI
