import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Filter

theorem eventually_quadratic_prime_exponent (K A B : ℝ) {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, K*L^2-c*Real.exp (α*L) ≤ -A*L-B := by
  have ht : Tendsto (fun L : ℝ => c*(Real.exp (α*L)/L^2)) atTop atTop := by
    apply Tendsto.const_mul_atTop hc
    simpa only [Real.rpow_two] using tendsto_exp_mul_div_rpow_atTop (2 : ℝ) α hα
  filter_upwards [ht.eventually_ge_atTop (|K|+|A|+|B|),
    eventually_ge_atTop (1 : ℝ)] with L he hL
  have hL0 : 0 < L := by linarith
  have hL2 : 0 < L^2 := pow_pos hL0 _
  have hE : (|K|+|A|+|B|)*L^2 ≤ c*Real.exp (α*L) := by
    apply (le_div_iff₀ hL2).mp
    simpa only [mul_div_assoc] using he
  have hLL : L ≤ L^2 := by nlinarith
  have h1L : (1 : ℝ) ≤ L^2 := by nlinarith
  have hK := mul_le_mul_of_nonneg_right (le_abs_self K) hL2.le
  have hA := (mul_le_mul_of_nonneg_right (le_abs_self A) hL0.le).trans
    (mul_le_mul_of_nonneg_left hLL (abs_nonneg A))
  have hB := (le_abs_self B).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h1L (abs_nonneg B))
  nlinarith

theorem exp_quarter_target (d B r m : ℝ) :
    Real.exp (-d-2*B*r*m-Real.log 4) =
      (1/4 : ℝ)*Real.exp (-d)*Real.exp (-2*B*r*m) := by
  have he : -d-2*B*r*m-Real.log 4 = -Real.log 4+(-d)+(-2*B*r*m) := by ring
  rw [he,Real.exp_add,Real.exp_add,Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ)<4)]
  norm_num

def diagonalGapThreshold (B β C : ℝ) : ℝ :=
  2*|B|+2*|β+1|+|C|+|Real.log 2|+6

theorem diagonalGapThreshold_pos (B β C : ℝ) :
    0 < diagonalGapThreshold B β C := by
  unfold diagonalGapThreshold
  positivity

theorem diagonal_good_exponent (B β C BD r m L z O d : ℝ)
    (hBD : diagonalGapThreshold B β C ≤ BD)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hL : 0 ≤ L) (hLm : L ≤ 2*m)
    (hz : 0 ≤ Real.log z) (hO : O+Real.log 4 ≤ m) (hd : d ≤ m) :
    -(r*(BD+20*Real.log z)*m)+r*m*(Real.log z+C+Real.log 2)+
      (β+1)*r*L+m+O ≤ -d-2*B*r*m-Real.log 4 := by
  have hr0 : 0 ≤ r := by linarith
  have hrm : 0 ≤ r*m := mul_nonneg hr0 hm
  have hmm : m ≤ r*m := by nlinarith
  have hmain : 2*|B|+2*|β+1|+C+Real.log 2+6 ≤ BD := by
    dsimp only [diagonalGapThreshold] at hBD
    linarith [le_abs_self C,le_abs_self (Real.log 2)]
  have hcost := mul_le_mul_of_nonneg_right hmain hrm
  have hβ : (β+1)*r*L ≤ 2*|β+1| *(r*m) := by
    calc
      _ ≤ |β+1| *r*L := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self (β+1)) hr0) hL
      _ ≤ |β+1| *r*(2*m) := mul_le_mul_of_nonneg_left hLm (by positivity)
      _ = _ := by ring
  have hB := mul_le_mul_of_nonneg_right (le_abs_self B) hrm
  have hlog : 0 ≤ Real.log z*(r*m) := mul_nonneg hz hrm
  nlinarith

end Ostmann.Characters.DiagonalEstimate

end

end OAI
