import OAI.Analysis.PlanarPacking.CoefficientClose

namespace OAI

/-!
# Tails of the interpolation coefficients

Truncating a summable coefficient family contracts its norm. The finite rational
table for OpenAI's sharp planar Fourier construction bounds the tails of the
exact coefficients through the coefficient error estimate.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
noncomputable def tailList (x : X) (N : ℕ) : X :=
  ⟨(fun k => if N<k.1.val then x k else 0), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs,apply_ite,abs_zero]
      using tailScalar_summable x N⟩
lemma tailList_apply (x : X) (N : ℕ) (k : Node×Bool) :
    tailList x N k=if N<k.1.val then x k else 0 := rfl
lemma tailList_norm (x : X) (N : ℕ) : ‖tailList x N‖=rowTailNorm x N := by
  rw [X_norm_scalar,← tailScalar_eq]
  apply tsum_congr; intro k
  simp only [tailList_apply]
  split_ifs <;> simp
lemma tailList_contraction (x : X) (N : ℕ) : ‖tailList x N‖ ≤ ‖x‖ := by
  rw [X_norm_scalar,X_norm_scalar]
  exact (X_summable (tailList x N)).tsum_le_tsum
    (fun k => by simp only [tailList_apply]; split_ifs <;> simp [abs_nonneg]) (X_summable x)
lemma tailList_sub (x y : X) (N : ℕ) : tailList (x-y) N=tailList x N-tailList y N := by
  ext k
  simp only [tailList_apply,lp.coeFn_sub,Pi.sub_apply]
  split_ifs <;> simp
lemma tailList_table (a : Bool) (N : ℕ) :
    tailList (tableList a) N=IF (RF (tailList (tableList a) N)) := by
  ext k
  rw [finiteProjection_apply finiteIndex finiteIndex_injective]
  by_cases hk : ∃ i,finiteIndex i=k
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk]
    have hgt : 100<k.1.val := by
      have hh:=finiteIndex_range k.1 k.2
      have hn : ¬k.1.val≤100 := by intro h; exact hk (hh.mpr h)
      omega
    simp only [tailList_apply,tableList_apply,tableD_large a hgt,tableC_large a hgt,
      Rat.cast_zero,ite_self]
lemma tailList_table_norm (a : Bool) (N : ℕ) :
    ‖tailList (tableList a) N‖=
      ((∑ i : FiniteIndex,if N<(finiteIndex i).1.val then |tableCoordRat a (finiteIndex i)| else 0 : ℚ):ℝ) := by
  rw [tailList_table a N,finiteEmbedding_norm finiteIndex finiteIndex_injective,l1Finite_norm]
  simp only [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteRestriction_apply,tailList_apply,tableList_apply]
  simp only [tableCoordRat]
  split_ifs <;> simp_all
lemma tailList_table_bound (a : Bool) : ‖tailList (tableList a) 40‖ < (2:ℝ)/10^5 := by
  rw [tailList_table_norm]
  have hh : (∑ i : FiniteIndex,if 40<(finiteIndex i).1.val then |tableCoordRat a (finiteIndex i)| else 0 : ℚ)<2/10^5 := by
    cases a <;> decide +kernel
  have hr : ((∑ i : FiniteIndex,if 40<(finiteIndex i).1.val then |tableCoordRat a (finiteIndex i)| else 0 : ℚ):ℝ)<((2/10^5:ℚ):ℝ) := Rat.cast_lt.mpr hh
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] at hr
  norm_num at hr ⊢
  exact hr
lemma exact_tail_norm (a : Bool) : ‖tailList (exactList a) 40‖ < (5:ℝ)/10^5 := by
  have he : exactList a=tableList a-coefficientError a := by unfold coefficientError; abel
  rw [he,tailList_sub]
  have hh:=norm_sub_le (tailList (tableList a) 40) (tailList (coefficientError a) 40)
  have hc:=tailList_contraction (coefficientError a) 40
  linarith [tailList_table_bound a,coefficient_error_bound a]
end SharpPlanar

end OAI
