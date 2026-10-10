import OAI.GroupTheory.Thompson.Model
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

/-!
# Positive normalized left-invariant means

The domain is the actual space of all bounded real functions on the group.
Continuity is a consequence of positivity and normalization, not an assumption.
-/

noncomputable section

open scoped ENNReal

universe uG

namespace ThompsonNonamenability

@[simp]
theorem BoundedReal.smul_one_apply {G : Type uG} (r : ℝ) (g : G) :
    (r • (1 : BoundedReal G)) g = r := by
  simp [lp.coeFn_smul, lp.infty_coeFn_one]

variable {G : Type uG} [Group G]

@[simp]
theorem leftPull_apply (h : G) (f : BoundedReal G) (g : G) :
    leftPull h f g = f (h * g) := rfl

@[simp]
theorem leftPull_one (f : BoundedReal G) : leftPull (1 : G) f = f := by
  apply lp.ext
  funext g
  simp

/-- Pullback reverses the order of the two left multiplications. -/
theorem leftPull_mul (h k : G) (f : BoundedReal G) :
    leftPull (h * k) f = leftPull k (leftPull h f) := by
  apply lp.ext
  funext g
  simp [mul_assoc]

namespace InvariantMean

instance : CoeFun (InvariantMean G) (fun _ => BoundedReal G → ℝ) :=
  ⟨fun M => M.toLinearMap⟩

@[simp]
theorem map_zero (M : InvariantMean G) : M 0 = 0 := M.toLinearMap.map_zero

@[simp]
theorem map_add (M : InvariantMean G) (f g : BoundedReal G) :
    M (f + g) = M f + M g := M.toLinearMap.map_add f g

@[simp]
theorem map_sub (M : InvariantMean G) (f g : BoundedReal G) :
    M (f - g) = M f - M g := M.toLinearMap.map_sub f g

@[simp]
theorem map_smul (M : InvariantMean G) (r : ℝ) (f : BoundedReal G) :
    M (r • f) = r * M f := by
  simpa only [smul_eq_mul] using M.toLinearMap.map_smul r f

/-- Evaluation of a constant function. -/
@[simp]
theorem map_const (M : InvariantMean G) (r : ℝ) :
    M (r • (1 : BoundedReal G)) = r := by
  rw [map_smul, M.normalized, mul_one]

/-- Positivity gives monotonicity for the pointwise order. -/
theorem mono (M : InvariantMean G) {f g : BoundedReal G}
    (hfg : ∀ x, f x ≤ g x) : M f ≤ M g := by
  have h := M.positive (g - f) (fun x => sub_nonneg.mpr (hfg x))
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- A mean has norm at most one, as a consequence of its defining axioms. -/
theorem abs_apply_le_norm (M : InvariantMean G) (f : BoundedReal G) :
    |M f| ≤ ‖f‖ := by
  have hbound (g : G) : -‖f‖ ≤ f g ∧ f g ≤ ‖f‖ := by
    apply abs_le.mp
    simpa only [Real.norm_eq_abs] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero f g
  have hlo := M.mono (f := (-‖f‖) • (1 : BoundedReal G)) (g := f)
    (fun g => by simpa only [BoundedReal.smul_one_apply] using (hbound g).1)
  have hhi := M.mono (f := f) (g := ‖f‖ • (1 : BoundedReal G))
    (fun g => by simpa only [BoundedReal.smul_one_apply] using (hbound g).2)
  rw [map_const] at hlo hhi
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- The continuous functional furnished automatically by a positive normalized mean. -/
def toContinuousLinearMap (M : InvariantMean G) : BoundedReal G →L[ℝ] ℝ :=
  M.toLinearMap.mkContinuous 1 (fun f => by
    simpa only [one_mul, Real.norm_eq_abs] using M.abs_apply_le_norm f)

@[simp]
theorem toContinuousLinearMap_apply (M : InvariantMean G) (f : BoundedReal G) :
    M.toContinuousLinearMap f = M f := rfl

theorem continuous (M : InvariantMean G) : Continuous M :=
  M.toContinuousLinearMap.continuous

theorem norm_toContinuousLinearMap_le_one (M : InvariantMean G) :
    ‖M.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [toContinuousLinearMap_apply, one_mul, Real.norm_eq_abs] using
    M.abs_apply_le_norm f

/-- Normalization makes the automatic functional's operator norm exactly one. -/
theorem norm_toContinuousLinearMap (M : InvariantMean G) :
    ‖M.toContinuousLinearMap‖ = 1 := by
  apply le_antisymm M.norm_toContinuousLinearMap_le_one
  have h := M.toContinuousLinearMap.le_opNorm (1 : BoundedReal G)
  simpa only [toContinuousLinearMap_apply, M.normalized, norm_one, mul_one] using h

end InvariantMean

end ThompsonNonamenability

end

end OAI
