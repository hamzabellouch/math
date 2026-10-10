import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterLocalZeroCount

namespace OAI

/-! # Actual analytic multiplicities of character zeros

The divisor on the whole plane is used consistently, so local disk counts
and later sums over finitely many zeros count the same multiplicities.
-/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators Classical

theorem PrimitiveComplexCharacter.L_analytic (χ : PrimitiveComplexCharacter) (z : ℂ) :
    AnalyticAt ℂ χ.L z := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact (DirichletCharacter.differentiable_LFunction χ.nontrivial).analyticAt z

theorem PrimitiveComplexCharacter.L_order_ne_top (χ : PrimitiveComplexCharacter) (z : ℂ) :
    analyticOrderAt χ.L z ≠ ⊤ := by
  intro h
  have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z χ.L_analytic).mp h
  have hn := χ.L_lower_re_two (2 : ℂ) (by norm_num)
  rw [he] at hn
  norm_num at hn

noncomputable def characterZeroOrder (χ : PrimitiveComplexCharacter) (z : ℂ) : ℤ :=
  divisor χ.L univ z

theorem characterZeroOrder_nonneg (χ : PrimitiveComplexCharacter) (z : ℂ) :
    0 ≤ characterZeroOrder χ z :=
  (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z).divisor_nonneg z

theorem characterZeroOrder_eq_local (χ : PrimitiveComplexCharacter) (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (13 / 8 : ℝ)) :
    characterZeroOrder χ z =
      divisor χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ)) z := by
  simp only [characterZeroOrder, AnalyticOnNhd.divisor_apply
    (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z) (mem_univ z),
    AnalyticOnNhd.divisor_apply
    (show AnalyticOnNhd ℂ χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ)) from
      fun z _ => χ.L_analytic z) hz]

theorem characterZeroOrder_sum_le_local (χ : PrimitiveComplexCharacter) (t : ℝ)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ closedBall (characterZeroCenter t) (13 / 8 : ℝ)) :
    ∑ z ∈ S, characterZeroOrder χ z ≤ characterLocalZeroMass χ t := by
  let D := divisor χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ))
  have hfin := D.finiteSupport (isCompact_closedBall (characterZeroCenter t) (13 / 8 : ℝ))
  have hnonneg : ∀ z, 0 ≤ D z :=
    (show AnalyticOnNhd ℂ χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ)) from
      fun z _ => χ.L_analytic z).divisor_nonneg
  calc
    _ = ∑ z ∈ S, D z := Finset.sum_congr rfl (fun z hz => characterZeroOrder_eq_local χ t z (hS z hz))
    _ ≤ ∑ z ∈ S ∪ hfin.toFinset, D z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro z _ _
      exact hnonneg z
    _ = ∑ᶠ z, D z := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro z hz
      exact Finset.mem_union_right _ (hfin.mem_toFinset.mpr hz)

end Ostmann

end OAI
