import OAI.MeasureTheory.Falconer.Estimates.TripleColumns
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowMap

namespace OAI

/-! # Quantitative inverse bounds for the actual three-direction frame -/

namespace Falconer
open scoped BigOperators

theorem tripleCofactors_norm_le_one {u v w : Space 3}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (i : Fin 3) :
    ‖tripleCofactors u v w i‖ ≤ 1 := by
  fin_cases i
  · exact euclideanCross_norm_le_one hv hw
  · exact euclideanCross_norm_le_one hw hu
  · exact euclideanCross_norm_le_one hu hv

theorem tripleDualCoordinates_norm {u v w : Space 3}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (x : Space 3) :
    ‖tripleDualCoordinates u v w x‖ ≤ (3/|inner ℝ u (euclideanCross v w)|)*‖x‖ := by
  have hh := coordinate_norm_le_card_mul (tripleDualCoordinates u v w x)
    (r := ‖x‖/|inner ℝ u (euclideanCross v w)|) (by
      intro i
      change |inner ℝ (tripleCofactors u v w i) x / inner ℝ u (euclideanCross v w)| ≤ _
      rw [abs_div]
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      exact (abs_real_inner_le_norm _ _).trans (by
        have hi := tripleCofactors_norm_le_one hu hv hw i
        nlinarith [norm_nonneg x]))
  norm_num only [Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

theorem tripleColumnLinear_norm {u v w : Space 3}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (x : Space 3) :
    ‖tripleColumnLinear u v w x‖ ≤ 3*‖x‖ := by
  have hn (i : Fin 3) : ‖![u,v,w] i‖ ≤ 1 := by
    fin_cases i
    · exact hu
    · exact hv
    · exact hw
  calc
    _ ≤ ∑ i : Fin 3, ‖x i • (![u,v,w] i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      have hx : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
      exact (mul_le_mul hx (hn i) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

theorem exists_transverse_triple_frame {u v w : Space 3}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgram : Δ ≤ Real.sqrt (tripleGram u v w)) :
    ∃ e : Space 3 ≃L[ℝ] Space 3,
      (∀ x, e x = tripleColumnLinear u v w x) ∧
      (∀ i j : Fin 3, j ≠ i → (e.symm (![u,v,w] i)) j = 0) ∧
      ‖e.toContinuousLinearMap‖ ≤ 3 ∧ ‖e.symm.toContinuousLinearMap‖ ≤ 3/Δ := by
  have heq : Real.sqrt (tripleGram u v w) = |inner ℝ u (euclideanCross v w)| := by
    rw [← euclideanCross_triple_sq,Real.sqrt_sq_eq_abs]
  have ht : inner ℝ u (euclideanCross v w) ≠ 0 := by
    have hh := hΔ.trans_le hgram
    rw [heq] at hh
    exact abs_pos.mp hh
  let e := tripleColumnEquiv u v w ht
  refine ⟨e,fun _ => rfl,?_,?_,?_⟩
  · intro i j hji
    rw [tripleColumnEquiv_symm_apply]
    change inner ℝ (tripleCofactors u v w j) (![u,v,w] i) /
      inner ℝ u (euclideanCross v w) = 0
    rw [tripleCofactors_inner,ite_eq_right hji,zero_div]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    exact tripleColumnLinear_norm hu hv hw
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖e.symm x‖ ≤ _
    rw [tripleColumnEquiv_symm_apply]
    apply (tripleDualCoordinates_norm hu hv hw x).trans
    have hh : 3/|inner ℝ u (euclideanCross v w)| ≤ 3/Δ := by
      rw [← heq]
      gcongr
    exact mul_le_mul_of_nonneg_right hh (norm_nonneg x)

end Falconer

end OAI
