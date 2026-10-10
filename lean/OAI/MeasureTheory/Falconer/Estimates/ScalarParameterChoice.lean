import OAI.MeasureTheory.Falconer.Estimates.ScalarRegularizationBudget

namespace OAI

/-! Choosing the fixed scalar block parameters. The resulting projection
 gain dominates the loss of the initial dyadic regularization. -/
namespace Falconer

 theorem scalar_block_parameters {κ : ℝ} (hκ : 0 < κ) (K : ℝ) :
    ∃ P B C : ℕ, 18 ≤ P ∧ 7 ≤ C ∧ 2*C ≤ B ∧
      800*(P:ℝ) ≤ κ*(B:ℝ) ∧ 8*(C:ℝ) ≤ κ*(B:ℝ) ∧
      Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
        κ*(C:ℝ)*Real.log 2 ∧
      Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200 := by
  let l := Real.log 2
  have hl : 0 < l := Real.log_pos (by norm_num)
  let A := Real.log (64*K)+κ*Real.log (5/4:ℝ)
  obtain ⟨D,hD⟩ := exists_nat_gt (max 7 ((|A|+4001*l)/(κ*l)))
  have hD7 : 7 ≤ D := by
    exact_mod_cast (show (7:ℝ) ≤ D from le_of_lt ((le_max_left _ _).trans_lt hD))
  have hDscalar : |A|+4001*l ≤ κ*(D:ℝ)*l := by
    have hh := (div_lt_iff₀ (mul_pos hκ hl)).1 ((le_max_right _ _).trans_lt hD)
    nlinarith
  have hkD : 4001 ≤ κ*(D:ℝ) := by nlinarith [abs_nonneg A]
  let β := Real.log 2050+2*Real.log ((D:ℝ)^2+1)
  have hβ : 0 ≤ β := add_nonneg (Real.log_nonneg (by norm_num))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg (D:ℝ)])))
  obtain ⟨n,hn5,hn⟩ := scalar_square_dominates_linear
    (show 0 < κ*l/200 by positivity) hβ
  let P := n^2
  let C := D*P
  let B := D^2*P
  have hP18 : 18 ≤ P := by dsimp [P]; nlinarith
  have hP1 : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast (show 1 ≤ P by omega)
  have hP0 : (0:ℝ) ≤ (P:ℝ) := Nat.cast_nonneg _
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
  have hC7 : 7 ≤ C := by
    have hh := Nat.mul_le_mul_left D (show 1 ≤ P by omega)
    dsimp [C]
    omega
  have h2CB : 2*C ≤ B := by
    have hh : 2*D ≤ D^2 := by nlinarith
    have hm := Nat.mul_le_mul_right P hh
    dsimp [C,B]
    nlinarith
  refine ⟨P,B,C,hP18,hC7,h2CB,?_,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hkD (Nat.cast_nonneg D)
    have hd2 : 800 ≤ κ*(D:ℝ)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hd2 hP0
    dsimp [B]
    push_cast
    nlinarith
  · have hh : 8 ≤ κ*(D:ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_right hh (mul_nonneg (Nat.cast_nonneg D) hP0)
    dsimp [C,B]
    push_cast
    nlinarith
  · have hm := mul_le_mul_of_nonneg_right hDscalar hP0
    have ha := mul_le_mul_of_nonneg_left hP1 (abs_nonneg A)
    dsimp [C]
    push_cast
    change A+4000*(P:ℝ)*l ≤ κ*((D:ℝ)*(P:ℝ))*l
    nlinarith [le_abs_self A]
  · have hr := scalar_regularization_log_bound D n (by omega)
    dsimp [B,P]
    push_cast
    change Real.log (2050*((D:ℝ)^2*(n:ℝ)^2+1)^2) ≤ κ*(n:ℝ)^2*l/200
    calc
      _ ≤ Real.log 2050+2*Real.log ((D:ℝ)^2+1)+4*(n:ℝ) := hr
      _ ≤ (κ*l/200)*(n:ℝ)^2 := hn
      _ = _ := by ring

end Falconer

end OAI
