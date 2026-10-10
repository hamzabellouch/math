import OAI.NumberTheory.JointDickman.Analysis.LaplaceTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # Removing a fixed upper cutoff from Laplace moments -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics
open scoped Topology

 theorem fractional_laplace_tail_isBigO {z η : ℝ} (hz1 : z < 1) (hη : 0 ≤ η) (j : ℕ) :
    (fun L : ℝ => ∫ t : ℝ in Ioi η, t^((j:ℝ)-z)*Real.exp (-(L*t)))
      =O[atTop] (fun L => Real.exp (-(η/2)*L)) := by
  refine isBigO_iff.mpr ⟨Real.Gamma ((j:ℝ)+1-z),?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hn : 0 ≤ ∫ t : ℝ in Ioi η, t^((j:ℝ)-z)*Real.exp (-(L*t)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hη.trans ht.le) _) (Real.exp_pos _).le
  have hg : 0 ≤ Real.Gamma ((j:ℝ)+1-z) :=
    (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)).le
  rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(L*η/2))*(L/2)^(z-j-1)*Real.Gamma ((j:ℝ)+1-z) :=
      fractional_laplace_tail_bound hz1 hL0 hη j
    _ ≤ Real.exp (-(L*η/2))*1*Real.Gamma ((j:ℝ)+1-z) := by
      apply mul_le_mul_of_nonneg_right _ hg
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    _ = _ := by rw [show -(L*η/2) = -(η/2)*L by ring]; ring

 theorem fractional_laplace_tail_isLittleO {z η : ℝ} (hz1 : z < 1) (hη : 0 < η) (j : ℕ) (b : ℝ) :
    (fun L : ℝ => ∫ t : ℝ in Ioi η, t^((j:ℝ)-z)*Real.exp (-(L*t)))
      =o[atTop] (fun L => L^b) :=
  (fractional_laplace_tail_isBigO hz1 hη.le j).trans_isLittleO
    (isLittleO_exp_neg_mul_rpow_atTop (by linarith : 0 < η/2) b)

 theorem fractional_laplace_cutoff_error {z η : ℝ} (hz1 : z < 1) (hη : 0 < η) (j : ℕ) (b : ℝ) :
    (fun L : ℝ => (∫ t : ℝ in Ioc 0 η, t^((j:ℝ)-z)*Real.exp (-(L*t))) -
      L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) =o[atTop] (fun L => L^b) := by
  apply ((fractional_laplace_tail_isLittleO hz1 hη j b).neg_left).congr' _ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have he := intervalIntegral.integral_Ioi_sub_Ioi (fractional_laplace_integrable hz1 hL j) hη.le
  rw [intervalIntegral.integral_of_le hη.le,fractional_laplace_gamma hz1 hL j] at he
  linarith

end JointDickman

end OAI
