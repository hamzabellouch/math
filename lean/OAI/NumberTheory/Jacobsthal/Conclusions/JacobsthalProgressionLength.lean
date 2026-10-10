import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalSourceRounding

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.JacobsthalProgressionLength
open ProgressionSieve

theorem progression_real_bounds (Y Z : ℕ) :
    (Y:ℝ)/((Z:ℝ)+1) ≤ (progressionLength Y Z:ℝ) ∧
      (progressionLength Y Z:ℝ) ≤ (Y:ℝ)/((Z:ℝ)+1)+1 := by
  constructor
  · have hdiv := Nat.mod_add_div Y (Z+1)
    have hmod := Nat.mod_lt Y (Nat.succ_pos Z)
    have hn : Y ≤ (Y/(Z+1)+1)*(Z+1) := by nlinarith
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(Z:ℝ)+1)).mpr
    exact_mod_cast hn
  · have hh : ((Y/(Z+1):ℕ):ℝ) ≤ (Y:ℝ)/((Z+1:ℕ):ℝ) := Nat.cast_div_le
    push_cast at hh
    simp only [progressionLength,Nat.cast_add,Nat.cast_one]
    linarith

theorem source_progression_bounds {x l : ℝ} (hx : 4 ≤ x) (hl : 2 ≤ l)
    (hlx : l^2 ≤ x) (Y Z : ℕ)
    (hYlo : x^2/8 ≤ (Y:ℝ)) (hYhi : (Y:ℝ) ≤ x^2)
    (hZlo : x*l/2 ≤ (Z:ℝ)) (hZhi : (Z:ℝ)+1 ≤ 2*x*l)
    (hZstrict : x*l < (Z:ℝ)+1) :
    x/(16*l) ≤ (progressionLength Y Z:ℝ) ∧
      (progressionLength Y Z:ℝ) ≤ 2*x/l ∧ progressionLength Y Z ≤ Z := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < l := by linarith
  have hZ0 : (0:ℝ)<(Z:ℝ)+1 := by positivity
  have hT := progression_real_bounds Y Z
  have hlo : x/(16*l) ≤ (progressionLength Y Z:ℝ) := by
    calc
      _ = (x^2/8)/(2*x*l) := by field_simp; ring
      _ ≤ (x^2/8)/((Z:ℝ)+1) :=
        div_le_div_of_nonneg_left (by positivity) hZ0 hZhi
      _ ≤ (Y:ℝ)/((Z:ℝ)+1) := div_le_div_of_nonneg_right hYlo hZ0.le
      _ ≤ _ := hT.1
  have hhi : (progressionLength Y Z:ℝ) ≤ 2*x/l := by
    have hlx' : l ≤ x := by nlinarith
    have hone : 1 ≤ x/l := (one_le_div hl0).mpr hlx'
    calc
      _ ≤ (Y:ℝ)/((Z:ℝ)+1)+1 := hT.2
      _ ≤ x^2/((Z:ℝ)+1)+1 := by
        have hh := div_le_div_of_nonneg_right hYhi hZ0.le
        linarith
      _ ≤ x^2/(x*l)+1 := by
        have hh := div_le_div_of_nonneg_left (sq_nonneg x) (mul_pos hx0 hl0) hZstrict.le
        linarith
      _ = x/l+1 := by field_simp
      _ ≤ 2*(x/l) := by linarith
      _ = _ := by ring
  refine ⟨hlo,hhi,?_⟩
  have hbound : 2*x/l ≤ x*l/2 := by
    apply (div_le_iff₀ hl0).mpr
    nlinarith
  exact_mod_cast hhi.trans (hbound.trans hZlo)

theorem progression_log_lower {x l : ℝ} (hx : 0 < x) (hl : 0 < l)
    (hlarge : 16*l ≤ Real.sqrt x) (Y Z : ℕ)
    (hT : x/(16*l) ≤ (progressionLength Y Z:ℝ)) :
    Real.log x/2 ≤ Real.log (progressionLength Y Z:ℝ) := by
  have hs : Real.sqrt x ≤ x/(16*l) := by
    apply (le_div_iff₀ (by positivity : 0 < 16*l)).mpr
    have hh := mul_le_mul_of_nonneg_left hlarge (Real.sqrt_nonneg x)
    nlinarith [Real.sq_sqrt hx.le]
  have hh := Real.log_le_log (Real.sqrt_pos.mpr hx) (hs.trans hT)
  simpa only [Real.log_sqrt hx.le] using hh
end NumberTheoryLean.JacobsthalProgressionLength


end Erdos970

end OAI
