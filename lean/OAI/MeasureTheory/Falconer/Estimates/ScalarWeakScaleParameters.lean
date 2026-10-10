import OAI.MeasureTheory.Falconer.Geometry.ScalarNormalizationCost

namespace OAI

/-! One sufficiently small weak-loss exponent pays for all scalar
 normalization, fixed-fold sumset and prefix costs simultaneously. -/
namespace Falconer

 theorem scalar_weak_scale_parameters {κ η c p q : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q) (B copies : ℕ) (hB : 0 < B) :
    ∃ ε : ℝ, ∃ M0 : ℕ, 0 < ε ∧ 0 < M0 ∧ ∀ M : ℕ, M0 ≤ M →
      let x := (B:ℝ)*(M:ℝ)*Real.log 2
      ε*x ≤ κ^2*x/160 ∧
      Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log 2+(copies:ℝ)*ε*x ≤ κ*x/4 ∧
      (2*ε-κ)*x ≤ 0 ∧ κ*Real.log 2+(ε-κ)*x < 0 ∧
      c+(p+q)*ε*x ≤ η*(M:ℝ)*Real.log 2 := by
  have hBR : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε := min (κ^2/320) (min (κ/(8*((copies:ℝ)+1)))
    (min (κ/4) (η/(4*(B:ℝ)*(p+q+1)))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he1 : ε ≤ κ^2/320 := min_le_left _ _
  have he2 : ε ≤ κ/(8*((copies:ℝ)+1)) := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : ε ≤ κ/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he4 : ε ≤ η/(4*(B:ℝ)*(p+q+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hecopies : (copies:ℝ)*ε ≤ κ/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*((copies:ℝ)+1))).1 he2
    nlinarith
  have hecost : (p+q)*ε*(B:ℝ) ≤ η/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(B:ℝ)*(p+q+1))).1 he4
    have hn : 0 ≤ ε*(B:ℝ) := by positivity
    nlinarith
  let d := Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log 2
  obtain ⟨M0,hM0⟩ := exists_nat_gt (max 3
    (max (2*c/(η*Real.log 2)) (8*d/(κ*(B:ℝ)*Real.log 2))))
  have hM03 : 3 ≤ M0 := by
    exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hM0))
  have hc0 : 2*c ≤ η*(M0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (mul_pos hη hl)).1
      ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hM0))
    nlinarith
  have hd0 : 8*d ≤ κ*(B:ℝ)*(M0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (mul_pos (mul_pos hκ hBR) hl)).1
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hM0))
    nlinarith
  refine ⟨ε,M0,hε,by omega,?_⟩
  intro M hM
  dsimp only
  have hMR : (M0:ℝ) ≤ M := by exact_mod_cast hM
  have hM3 : (3:ℝ) ≤ M := by exact_mod_cast (hM03.trans hM)
  have hx : 0 ≤ (B:ℝ)*(M:ℝ)*Real.log 2 := by positivity
  have hcM : 2*c ≤ η*(M:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hMR (mul_nonneg hη.le hl.le)
    nlinarith
  have hdM : 8*d ≤ κ*(B:ℝ)*(M:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hMR (mul_nonneg (mul_nonneg hκ.le hBR.le) hl.le)
    nlinarith
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right he1 hx
    nlinarith [sq_nonneg κ]
  · have hh := mul_le_mul_of_nonneg_right hecopies hx
    dsimp [d] at hdM
    nlinarith
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
  · have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
    have hBM : (3:ℝ) ≤ (B:ℝ)*(M:ℝ) := by nlinarith
    have hlo := mul_le_mul_of_nonneg_right hBM (mul_nonneg hκ.le hl.le)
    have hhi := mul_le_mul_of_nonneg_right he3 hx
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hecost
      (show 0 ≤ (M:ℝ)*Real.log 2 by positivity)
    nlinarith

end Falconer

end OAI
