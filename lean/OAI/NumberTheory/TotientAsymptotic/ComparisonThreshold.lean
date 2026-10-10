import OAI.NumberTheory.TotientAsymptotic.FordParameterBounds

namespace OAI

/-! A fixed endpoint suffices for all quantitative band-sieve hypotheses. -/
noncomputable section
namespace TotientAsymptotic

lemma ford_comparison_threshold (R : ℝ) (hR : 0 < R) :
    ∃ y₀ : ℝ,1 < y₀ ∧ ∀ y : ℝ,y₀ ≤ y →
      Real.exp 2 ≤ y ∧ 1 ≤ B y ∧
      ∀ S : ℝ,1 ≤ B S → R ≤ Real.sqrt (B S*B y) := by
  let y₀ := Real.exp (Real.exp (R^2+2))
  have he : 2 ≤ Real.exp (R^2+2) := by nlinarith [Real.add_one_le_exp (R^2+2),sq_nonneg R]
  have hbase : Real.exp 2 ≤ y₀ := Real.exp_le_exp.mpr he
  have hy₀ : 1 < y₀ := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<2)).trans_le hbase
  refine ⟨y₀,hy₀,?_⟩
  intro y hy
  have hB : R^2+2 ≤ B y := by
    have hh := Real.log_le_log (Real.log_pos hy₀) (Real.log_le_log (by linarith) hy)
    simpa only [y₀,B,Real.log_exp] using hh
  refine ⟨hbase.trans hy,by nlinarith [sq_nonneg R],?_⟩
  intro S hS
  have hBy : 0 ≤ B y := by nlinarith [sq_nonneg R]
  apply (Real.le_sqrt hR.le (mul_nonneg (by linarith) hBy)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hS (show 0 ≤ B y by nlinarith [sq_nonneg R])]

end TotientAsymptotic

end

end OAI
