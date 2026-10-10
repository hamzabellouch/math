import OAI.Analysis.PlanarPacking.Certificate.TableList

namespace OAI

/-!
# Norm bounds for the rational coefficient family

Finite rational sums give bounds for the mass of the cardinal coefficients.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
noncomputable def tableCoordRat (a : Bool) (ni : Node×Bool) : ℚ :=
  if ni.2 then tableD a ni.1.val else tableC a ni.1.val
noncomputable def tableFiniteNormRat (a : Bool) : ℚ := ∑ i : FiniteIndex, |tableCoordRat a (finiteIndex i)|
lemma tableList_norm (a : Bool) : ‖tableList a‖=(tableFiniteNormRat a:ℝ) := by
  have he : tableList a=IF (RF (tableList a)) := sub_eq_zero.mp (tableList_discard a)
  calc
    ‖tableList a‖=‖IF (RF (tableList a))‖ := congrArg norm he
    _=‖RF (tableList a)‖ := finiteEmbedding_norm finiteIndex finiteIndex_injective _
    _=(tableFiniteNormRat a:ℝ) := by
      rw [l1Finite_norm]
      simp only [tableFiniteNormRat,Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      change |tableList a (finiteIndex i)|= _
      rw [tableList_apply]
      by_cases hi : (finiteIndex i).2=true <;> simp [tableCoordRat,hi]
lemma table_coeff_mass (a : Bool) :
    |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖ < (229:ℝ)/100 := by
  have hr : |tableC a 0|+|tableD a 0|+tableFiniteNormRat a<(229:ℚ)/100 := by
    cases a <;> decide +kernel
  change |(tableC a 0:ℝ)|+|(tableD a 0:ℝ)|+‖tableList a‖ < _
  rw [tableList_norm]
  have hr' : ((|tableC a 0|+|tableD a 0|+tableFiniteNormRat a:ℚ):ℝ)<((229/100:ℚ):ℝ) := Rat.cast_lt.mpr hr
  norm_num only [Rat.cast_add,Rat.cast_abs,Rat.cast_div,Rat.cast_ofNat] at hr'
  exact hr'
lemma table_constant_bound (a : Bool) : |(tableData a).C| ≤ (17:ℝ)/1000 := by
  cases a <;> norm_num [tableData,tableConstant]
end SharpPlanar

end OAI
