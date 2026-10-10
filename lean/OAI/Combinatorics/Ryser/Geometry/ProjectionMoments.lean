import OAI.Combinatorics.Ryser.Geometry.ProjectionPair
import OAI.Combinatorics.Ryser.Geometry.SliceEnergy
import OAI.Combinatorics.Ryser.Probability.Product
import OAI.Combinatorics.Ryser.Probability.Variance
import Mathlib.Algebra.Group.Units.Equiv

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F] [Fintype F]

theorem expectation_uniform_projection_pair (d e : Direction F) (hne : d ≠ e)
    (f g : F → ℝ) :
    (FiniteLaw.uniform (Point F)).expectation
        (fun p => f (projection d p) * g (projection e p)) =
      (FiniteLaw.uniform F).expectation f * (FiniteLaw.uniform F).expectation g := by
  calc
    _ = ((FiniteLaw.uniform (Point F)).map (projectionPairEquiv d e hne)).expectation
        (fun z : F × F => f z.1 * g z.2) := by
      rw [FiniteLaw.expectation_map]; rfl
    _ = ((FiniteLaw.uniform F).prod (FiniteLaw.uniform F)).expectation
        (fun z : F × F => f z.1 * g z.2) := by
      rw [FiniteLaw.map_uniform_equiv, FiniteLaw.uniform_prod]
    _ = (FiniteLaw.uniform F).expectation
        (fun t => f t * (FiniteLaw.uniform F).expectation g) := by
      rw [FiniteLaw.expectation_prod]
      simp only [FiniteLaw.expectation_smul]
    _ = _ := by
      simp only [FiniteLaw.expectation, ← mul_assoc, Finset.sum_mul]

theorem expectation_uniform_projection (d : Direction F) (f : F → ℝ) :
    (FiniteLaw.uniform (Point F)).expectation (fun p => f (projection d p)) =
      (FiniteLaw.uniform F).expectation f := by
  cases d with
  | none =>
      simpa only [FiniteLaw.expectation_const, mul_one] using
        expectation_uniform_projection_pair (F := F) none (some 0) (by simp)
          f (fun _ => 1)
  | some a =>
      simpa only [FiniteLaw.expectation_const, mul_one] using
        expectation_uniform_projection_pair (F := F) (some a) none (by simp)
          f (fun _ => 1)

theorem covariance_uniform_projection (d e : Direction F) (hne : d ≠ e)
    (f g : F → ℝ) :
    (FiniteLaw.uniform (Point F)).covariance
        (fun p => f (projection d p)) (fun p => g (projection e p)) = 0 := by
  rw [FiniteLaw.covariance_eq_expectation_mul_sub_mul,
    expectation_uniform_projection_pair d e hne f g,
    expectation_uniform_projection d f, expectation_uniform_projection e g,
    sub_self]

theorem expectation_uniform_projection_add (d : Direction F) (c : F) (f : F → ℝ) :
    (FiniteLaw.uniform (Point F)).expectation (fun p => f (projection d p + c)) =
      (FiniteLaw.uniform F).expectation f := by
  rw [expectation_uniform_projection d (fun t => f (t + c)),
    FiniteLaw.uniform_expectation, FiniteLaw.uniform_expectation]
  apply congrArg (fun s : ℝ => s / (Fintype.card F : ℝ))
  simpa only [Equiv.coe_addRight] using Equiv.sum_comp (Equiv.addRight c) f

variable [DecidableEq F]

theorem expectation_uniform_shifted_slice (U : Finset (Point F))
    (d : Direction F) (c : F) :
    (FiniteLaw.uniform (Point F)).expectation
        (fun p => (sliceCount U d (projection d p + c) : ℝ)) =
      (U.card : ℝ) / (Fintype.card F : ℝ) := by
  calc
    _ = (FiniteLaw.uniform F).expectation (fun t => (sliceCount U d t : ℝ)) :=
      expectation_uniform_projection_add d c _
    _ = _ := by rw [FiniteLaw.uniform_expectation, sum_sliceCount]

theorem variance_uniform_shifted_slice (U : Finset (Point F))
    (d : Direction F) (c : F) :
    (FiniteLaw.uniform (Point F)).variance
        (fun p => (sliceCount U d (projection d p + c) : ℝ)) =
      sliceEnergy U d := by
  unfold FiniteLaw.variance
  rw [expectation_uniform_shifted_slice]
  calc
    _ = (FiniteLaw.uniform F).expectation
        (fun t => ((sliceCount U d t : ℝ) -
          (U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2) :=
      expectation_uniform_projection_add d c _
    _ = sliceEnergy U d := by
      rw [FiniteLaw.uniform_expectation]; rfl

end RyserCoveringCounterexample

end

end OAI
