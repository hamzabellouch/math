import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! A bounded smooth test detecting a nonzero continuous finite-variation
martingale. Its bounded derivatives permit an integrable-variation argument. -/

noncomputable section
open Set
open scoped Topology

namespace SLEExactGauge

def massSeparationTest (x : ℝ) : ℝ := x^2 / (1+x^2)
def massSeparationSlope (x : ℝ) : ℝ := 2*x / (1+x^2)^2

theorem massSeparationTest_nonneg (x : ℝ) : 0 ≤ massSeparationTest x := by
  unfold massSeparationTest
  positivity

@[simp] theorem massSeparationTest_zero : massSeparationTest 0 = 0 := by
  norm_num [massSeparationTest]

@[simp] theorem massSeparationTest_eq_zero (x : ℝ) : massSeparationTest x = 0 ↔ x = 0 := by
  have hp : 0 < 1+x^2 := by positivity
  simp only [massSeparationTest,div_eq_zero_iff,hp.ne',or_false,pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)]

theorem massSeparationTest_hasDerivAt (x : ℝ) :
    HasDerivAt massSeparationTest (massSeparationSlope x) x := by
  have hd := ((hasDerivAt_id x).pow 2).div
    ((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)) (by positivity : 1+x^2 ≠ 0)
  convert hd using 1
  · rfl
  · dsimp only [massSeparationSlope,id_eq,Pi.pow_apply,Pi.add_apply,Pi.div_apply]
    field_simp
    ring

theorem massSeparationSlope_hasDerivAt (x : ℝ) :
    HasDerivAt massSeparationSlope ((2-6*x^2)/(1+x^2)^3) x := by
  have hd := ((hasDerivAt_id x).const_mul 2).div
    (((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)).pow 2)
    (by positivity : (1+x^2)^2 ≠ 0)
  convert hd using 1
  · rfl
  · dsimp only [id_eq,Pi.pow_apply,Pi.add_apply,Pi.div_apply]
    field_simp
    ring

theorem massSeparationSlope_abs_le (x : ℝ) : |massSeparationSlope x| ≤ 2 := by
  have hy : 0 ≤ x^2 := sq_nonneg x
  have hx : |x| ≤ 1+x^2 := by
    nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have hp : 0 < 1+x^2 := by positivity
  rw [massSeparationSlope,abs_div,abs_mul,abs_of_pos (sq_pos_of_pos hp)]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith [sq_nonneg (x^2)]

theorem massSeparationSlope_deriv_abs_le (x : ℝ) :
    |(2-6*x^2)/(1+x^2)^3| ≤ 8 := by
  have hp : 0 < 1+x^2 := by positivity
  rw [abs_div,abs_of_pos (pow_pos hp 3)]
  apply (div_le_iff₀ (pow_pos hp 3)).mpr
  have hn : |2-6*x^2| ≤ 2+6*x^2 := by
    have hh := abs_sub (2:ℝ) (6*x^2)
    norm_num [abs_mul,abs_of_nonneg (sq_nonneg x)] at hh ⊢
    exact hh
  have hb : 2+6*x^2 ≤ 8*(1+x^2)^3 := by
    nlinarith [sq_nonneg (x^2),pow_nonneg (sq_nonneg x) 3]
  exact hn.trans hb

theorem massSeparationTest_lipschitz (x y : ℝ) :
    |massSeparationTest y-massSeparationTest x| ≤ 2*|y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (univ:Set ℝ)) (f := massSeparationTest) (C := 2) (x := x) (y := y)
    (fun z _ => (massSeparationTest_hasDerivAt z).differentiableAt)
    (fun z _ => by simpa only [(massSeparationTest_hasDerivAt z).deriv,Real.norm_eq_abs]
      using massSeparationSlope_abs_le z) convex_univ (mem_univ x) (mem_univ y)
  simpa only [Real.norm_eq_abs] using h

theorem massSeparationSlope_lipschitz (x y : ℝ) :
    |massSeparationSlope y-massSeparationSlope x| ≤ 8*|y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (univ:Set ℝ)) (f := massSeparationSlope) (C := 8) (x := x) (y := y)
    (fun z _ => (massSeparationSlope_hasDerivAt z).differentiableAt)
    (fun z _ => by simpa only [(massSeparationSlope_hasDerivAt z).deriv,Real.norm_eq_abs]
      using massSeparationSlope_deriv_abs_le z) convex_univ (mem_univ x) (mem_univ y)
  simpa only [Real.norm_eq_abs] using h

theorem massSeparationTest_remainder_le (x y : ℝ) :
    |massSeparationTest y-massSeparationTest x-massSeparationSlope x*(y-x)| ≤ 8*|y-x|^2 := by
  let f (z : ℝ) := massSeparationTest z-massSeparationTest x-massSeparationSlope x*(z-x)
  have hd (z : ℝ) : HasDerivAt f (massSeparationSlope z-massSeparationSlope x) z := by
    convert ((massSeparationTest_hasDerivAt z).sub_const
      (massSeparationTest x)).sub (((hasDerivAt_id z).sub_const x).const_mul (massSeparationSlope x)) using 1
    · rfl
    · ring
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Metric.closedBall x |y-x|) (f := f) (C := 8*|y-x|) (x := x) (y := y)
    (fun z _ => (hd z).differentiableAt)
    (fun z hz => by
      rw [(hd z).deriv,Real.norm_eq_abs]
      exact (massSeparationSlope_lipschitz x z).trans
        (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,Real.dist_eq] using hz) (by norm_num)))
    (convex_closedBall x _) (Metric.mem_closedBall_self (abs_nonneg _))
    (by simp only [Metric.mem_closedBall,Real.dist_eq,le_refl])
  simpa only [f,sub_self,mul_zero,sub_zero,Real.norm_eq_abs,pow_two,mul_assoc] using h

theorem massSeparationTest_remainder_linear (x y : ℝ) :
    |massSeparationTest y-massSeparationTest x-massSeparationSlope x*(y-x)| ≤ 4*|y-x| := by
  calc
    _ ≤ |massSeparationTest y-massSeparationTest x|+|massSeparationSlope x*(y-x)| := abs_sub _ _
    _ ≤ 2*|y-x|+2*|y-x| := add_le_add (massSeparationTest_lipschitz x y)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (massSeparationSlope_abs_le x) (abs_nonneg _))
    _ = _ := by ring

end SLEExactGauge

end

end OAI
