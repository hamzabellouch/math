import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicWeight

namespace OAI

/-! Exact localization of the smoothing error to the two endpoint annuli. -/
noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeDyadicWeight_support_interval {J x : ℝ} (hJ : 1 ≤ J)
    (hx : primeDyadicWeight J hJ x ≠ 0) :
    Real.exp (-1/J) ≤ x ∧ x ≤ 2*Real.exp (1/J) := by
  have hxp : 0 < x := by
    by_contra h
    have hn : ¬0 < x := h
    exact hx (by change (if 0 < x then _ else 0)=0; rw [ite_eq_right hn])
  have hn : primeLogWindow J (-Real.log x) ≠ 0 := by
    change (if 0 < x then primeLogWindow J (-Real.log x) else 0) ≠ 0 at hx
    rwa [ite_eq_left hxp] at hx
  obtain ⟨hl,hr⟩ := primeLogWindow_support (by linarith) hn
  constructor
  · have h := Real.exp_le_exp.mpr (show -1/J ≤ Real.log x by simpa only [neg_div] using (show -(1/J) ≤ Real.log x by linarith))
    rwa [Real.exp_log hxp] at h
  · have h := Real.exp_le_exp.mpr (show Real.log x ≤ Real.log 2+1/J by linarith)
    rw [Real.exp_log hxp,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)] at h
    exact h

theorem primeDyadicWeight_boundary_error {α : Type*} (S : Finset α)
    (N : α → ℝ) (c : α → ℂ) {J X : ℝ} (hJ : 1 ≤ J) (hX : 0 < X) :
    ‖(∑ ν ∈ S, c ν*primeDyadicWeight J hJ (N ν/X))-
      (∑ ν ∈ S with X ≤ N ν ∧ N ν ≤ 2*X, c ν)‖ ≤
    ∑ ν ∈ S with
      (Real.exp (-1/J)*X ≤ N ν ∧ N ν < X) ∨
      (2*X < N ν ∧ N ν ≤ 2*Real.exp (1/J)*X), ‖c ν‖ := by
  have he : (∑ ν ∈ S, c ν*primeDyadicWeight J hJ (N ν/X))-
      (∑ ν ∈ S with X ≤ N ν ∧ N ν ≤ 2*X, c ν)=
      ∑ ν ∈ S, if X ≤ N ν ∧ N ν ≤ 2*X then 0 else
        c ν*primeDyadicWeight J hJ (N ν/X) := by
    rw [Finset.sum_filter,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ν hν
    by_cases hi : X ≤ N ν ∧ N ν ≤ 2*X
    · have hw := primeDyadicWeight_one hJ
        (show 1 ≤ N ν/X ∧ N ν/X ≤ 2 by
          constructor
          · exact (le_div_iff₀ hX).mpr (by simpa using hi.1)
          · exact (div_le_iff₀ hX).mpr hi.2)
      simp [hi,hw]
    · simp only [hi,ite_false,sub_zero]
  rw [he,Finset.sum_filter]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ν hν
  by_cases hi : X ≤ N ν ∧ N ν ≤ 2*X
  · simp only [hi,true_and,ite_true,norm_zero]
    split_ifs <;> positivity
  · simp only [hi,ite_false]
    by_cases hw : primeDyadicWeight J hJ (N ν/X)=0
    · simp only [hw,mul_zero,norm_zero]
      split_ifs <;> positivity
    · obtain ⟨hl,hr⟩ := primeDyadicWeight_support_interval hJ hw
      have hl' : Real.exp (-1/J)*X ≤ N ν := (le_div_iff₀ hX).mp hl
      have hr' : N ν ≤ 2*Real.exp (1/J)*X := (div_le_iff₀ hX).mp hr
      have hb : (Real.exp (-1/J)*X ≤ N ν ∧ N ν < X) ∨
          (2*X < N ν ∧ N ν ≤ 2*Real.exp (1/J)*X) := by
        by_cases hlo : N ν < X
        · exact Or.inl ⟨hl',hlo⟩
        · exact Or.inr ⟨lt_of_not_ge (fun h => hi ⟨le_of_not_gt hlo,h⟩),hr'⟩
      rw [ite_eq_left hb,norm_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (primeDyadicWeight_norm hJ _)

end CubicFirstMoment

end

end OAI
