import OAI.NumberTheory.TotientAsymptotic.ComparisonErrorBudget

namespace OAI

/-! The complete gridding error still leaves half of the strict exponent saving. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma collisionMesh_le_quarter_slack {h : ℕ} {δ : ℝ} (hh : 2≤h)
    (hδ : δ≤2/(h : ℝ)^32) : δ≤1/(4*(h : ℝ)^4) := by
  have hhR : (2 : ℝ)≤h := by exact_mod_cast hh
  have h0 : (0 : ℝ)<h := by linarith
  have hp : (8 : ℝ)≤(h : ℝ)^28 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) hhR 28
    norm_num at hp
    linarith
  apply hδ.trans
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<(h : ℝ)^32)
    (by positivity : (0 : ℝ)<4*(h : ℝ)^4)).mpr
  have he := mul_le_mul_of_nonneg_right hp (pow_nonneg h0.le 4)
  convert he using 1 <;> ring

/-- The extra endpoint normalization costs at most one mesh unit. Together
with every grid-width and normality term, it leaves exponent `-1-1/(2h^4)`. -/
theorem comparison_exponent_saving {b h : ℕ} {y S δ : ℝ} {Y U : ℕ → ℝ}
    (hbh : b≤h) (hh : 2≤h) (hδ : 0≤δ) (hδu : δ≤2/(h : ℝ)^32)
    (hmesh : Real.sqrt (B S/B y)=δ)
    (hweighted : (∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y)) ≤
      1-1/(h : ℝ)^4+δ+((2*(b : ℝ)+3)*δ)*(∑ j ∈ Finset.Icc 1 b, a j))
    (hwidth : ∀ j ∈ Finset.Icc 1 (b-1), B (Y j)/B y-B (U j)/B y≤(2*(b : ℝ)+3)*δ) :
    -2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+comparisonError b y S Y U ≤
      -1-1/(2*(h : ℝ)^4) := by
  have herr := comparisonError_le b y S Y U ((2*(b : ℝ)+3)*δ) hwidth
  rw [hmesh] at herr
  have hcost := comparison_grid_error_absorbed hbh hh hδ hδu
  have hd := collisionMesh_le_quarter_slack hh hδu
  have hdiff : ((b-1 : ℕ) : ℝ)≤b := by exact_mod_cast Nat.sub_le b 1
  have he0 : 0≤(2*(b : ℝ)+3)*δ := by positivity
  have he := mul_le_mul_of_nonneg_right (show 2*((b-1 : ℕ) : ℝ)≤2*b by linarith) he0
  have h0 : (0 : ℝ)<h := by exact_mod_cast (by omega : 0<h)
  have heq : 1/(2*(h : ℝ)^4)=2*(1/(4*(h : ℝ)^4)) := by ring
  rw [heq]
  have heq' : 1/(h : ℝ)^4=4*(1/(4*(h : ℝ)^4)) := by ring
  rw [heq'] at hweighted
  linarith

end TotientAsymptotic

end

end OAI
