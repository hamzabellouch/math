import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Ostmann.Tree.BottomPairCoordinates

namespace OAI

/-!
# The bottom-pair second moment

The valid difference/ratio coordinates identify the bottom-pair moment
with the contribution of ordered distinct nonzero pairs. In particular,
an `L²` bound suffices; no pointwise bound on the test is used.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance {K : Type*} [Field K] [Fintype K] :
    Fintype (ValidPairCoordinates K) := by
  classical
  unfold ValidPairCoordinates
  infer_instance

noncomputable local instance {K : Type*} [Field K] [Fintype K] :
    Fintype (DistinctNonzeroPair K) := by
  classical
  unfold DistinctNonzeroPair
  infer_instance

theorem pairCoordinate_sum_eq {K : Type*} [Field K] [Fintype K] (w : K → ℝ) :
    (∑ dt : ValidPairCoordinates K,
      w (dt.1.1 * dt.1.2 / (dt.1.2 - 1)) * w (dt.1.1 / (dt.1.2 - 1))) =
      ∑ xz : DistinctNonzeroPair K, w xz.1.1 * w xz.1.2 := by
  exact (pairCoordinatesEquiv K).bijective.sum_comp
    (fun xz : DistinctNonzeroPair K => w xz.1.1 * w xz.1.2)

theorem pairCoordinate_sum_le_square {K : Type*} [Field K] [Fintype K]
    (w : K → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ dt : ValidPairCoordinates K,
      w (dt.1.1 * dt.1.2 / (dt.1.2 - 1)) * w (dt.1.1 / (dt.1.2 - 1))) ≤
      (∑ x : K, w x) ^ 2 := by
  classical
  rw [pairCoordinate_sum_eq]
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun xz : K × K => xz.1 ≠ 0 ∧ xz.2 ≠ 0 ∧ xz.1 ≠ xz.2)
    (fun xz : K × K => w xz.1 * w xz.2)
  have hcomplement : 0 ≤ ∑ xz : {xz : K × K // ¬(xz.1 ≠ 0 ∧ xz.2 ≠ 0 ∧ xz.1 ≠ xz.2)},
      w xz.1.1 * w xz.1.2 :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (hw _) (hw _))
  have hfull : (∑ xz : K × K, w xz.1 * w xz.2) = (∑ x : K, w x) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring
  rw [hfull] at hsum
  change (∑ xz : {xz : K × K // xz.1 ≠ 0 ∧ xz.2 ≠ 0 ∧ xz.1 ≠ xz.2},
      w xz.1.1 * w xz.1.2) ≤ _
  linarith

/-- The unnormalized bottom-pair `L²` estimate. -/
theorem bottomPair_sum_norm_sq_le {K : Type*} [Field K] [Fintype K] (g : K → ℂ) :
    (∑ dt : ValidPairCoordinates K,
      ‖g (dt.1.1 * dt.1.2 / (dt.1.2 - 1)) * conj (g (dt.1.1 / (dt.1.2 - 1)))‖ ^ 2) ≤
      (∑ x : K, ‖g x‖ ^ 2) ^ 2 := by
  simpa only [norm_mul, Complex.norm_conj, mul_pow] using
    pairCoordinate_sum_le_square (fun x => ‖g x‖ ^ 2) (fun _ => sq_nonneg _)

/-- Equation `tree-R-mean`: the valid bottom-pair moment is bounded by
`(p/(p-1))²` when the field-probability squared norm is at most one. -/
theorem bottomPair_mean_norm_sq_le {p : ℕ} [Fact p.Prime] (g : ZMod p → ℂ)
    (hg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ dt : ValidPairCoordinates (ZMod p),
      ‖g (dt.1.1 * dt.1.2 / (dt.1.2 - 1)) * conj (g (dt.1.1 / (dt.1.2 - 1)))‖ ^ 2) /
      ((p : ℝ) - 1) ^ 2 ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
  have hnorm : 0 ≤ ∑ x : ZMod p, ‖g x‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hnum := (bottomPair_sum_norm_sq_le g).trans (sq_le_sq₀ hnorm hp |>.mpr hg)
  simpa only [div_pow] using div_le_div_of_nonneg_right hnum (sq_nonneg ((p : ℝ) - 1))

end Ostmann

end OAI
