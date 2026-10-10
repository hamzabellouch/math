import Mathlib.Analysis.Normed.Group.AddCircle
import OAI.NumberTheory.Ostmann.SharpSieveParseval

namespace OAI

open scoped BigOperators
open Set Complex

namespace Ostmann

noncomputable def circleTrigPoly (N : ℕ) (a : ℕ → ℂ) (θ : UnitAddCircle) : ℂ :=
  ∑ n ∈ Finset.range N, a n * fourier (n : ℤ) θ

@[simp]
theorem circleTrigPoly_coe (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    circleTrigPoly N a (t : UnitAddCircle) = trigPoly N a t := by
  simp only [circleTrigPoly, trigPoly, fourier_coe_apply, Int.cast_natCast,
    Complex.ofReal_one, div_one]

noncomputable def circleRepr (θ : UnitAddCircle) : ℝ := AddCircle.equivIco 1 0 θ

theorem circleRepr_mem_Ico (θ : UnitAddCircle) : circleRepr θ ∈ Ico (0 : ℝ) 1 := by
  simpa only [circleRepr, zero_add] using (AddCircle.equivIco 1 0 θ).property

theorem circleRepr_mem_Icc (θ : UnitAddCircle) : circleRepr θ ∈ Icc (0 : ℝ) 1 :=
  Ico_subset_Icc_self (circleRepr_mem_Ico θ)

@[simp]
theorem coe_circleRepr (θ : UnitAddCircle) : (circleRepr θ : UnitAddCircle) = θ :=
  AddCircle.coe_equivIco

theorem unitCircle_dist_coe_le_abs_sub (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ |x - y| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, ← Real.norm_eq_abs]
  exact QuotientAddGroup.norm_mk_le_norm

theorem circle_dist_le_abs_sub_repr (θ η : UnitAddCircle) :
    dist θ η ≤ |circleRepr θ - circleRepr η| := by
  simpa only [coe_circleRepr] using
    unitCircle_dist_coe_le_abs_sub (circleRepr θ) (circleRepr η)

theorem circleRepr_separated {ι : Type*} (θ : ι → UnitAddCircle) (δ : ℝ)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (θ i) (θ j)) :
    ∀ i j, i ≠ j → δ ≤ |circleRepr (θ i) - circleRepr (θ j)| := by
  intro i j hij
  exact (hsep i j hij).trans (circle_dist_le_abs_sub_repr (θ i) (θ j))

@[simp]
theorem trigPoly_circleRepr (N : ℕ) (a : ℕ → ℂ) (θ : UnitAddCircle) :
    trigPoly N a (circleRepr θ) = circleTrigPoly N a θ := by
  rw [← circleTrigPoly_coe, coe_circleRepr]

theorem sum_trigPoly_circleRepr_sq {ι : Type*} [Fintype ι]
    (N : ℕ) (a : ℕ → ℂ) (θ : ι → UnitAddCircle) :
    (∑ i, ‖trigPoly N a (circleRepr (θ i))‖ ^ 2) =
      ∑ i, ‖circleTrigPoly N a (θ i)‖ ^ 2 := by
  simp only [trigPoly_circleRepr]

end Ostmann

end OAI
