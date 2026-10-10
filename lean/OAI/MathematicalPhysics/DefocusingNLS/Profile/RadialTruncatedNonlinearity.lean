import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInitialEquation
import Mathlib.Algebra.Order.Ring.Abs

namespace OAI

/-! The bounded polynomial truncation used in the positive radial Dirichlet problem. -/

open Set
namespace DefocusingNLS

def radialAmplitudeClamp (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem radialAmplitudeClamp_mem (lo hi x : ℝ) (h : lo ≤ hi) :
    radialAmplitudeClamp lo hi x ∈ Icc lo hi :=
  ⟨le_max_left _ _,max_le h (min_le_left _ _)⟩

theorem radialAmplitudeClamp_eq (lo hi x : ℝ) (hx : x ∈ Icc lo hi) :
    radialAmplitudeClamp lo hi x=x := by
  simp only [radialAmplitudeClamp,min_eq_right hx.2,max_eq_right hx.1]

theorem radialAmplitudeClamp_lipschitz (lo hi : ℝ) :
    LipschitzWith 1 (radialAmplitudeClamp lo hi) :=
  (LipschitzWith.id.const_min hi).const_max lo

theorem unit_interval_power_difference (p : ℕ) (x y : ℝ)
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    ‖x^p-y^p‖ ≤ (p : ℝ)*‖x-y‖ := by
  have hm : max |x| |y| ≤ 1 := by
    rw [abs_of_nonneg hx.1,abs_of_nonneg hy.1]
    exact max_le hx.2 hy.2
  have hp : max |x| |y|^(p-1) ≤ 1 :=
    pow_le_one₀ ((abs_nonneg x).trans (le_max_left _ _)) hm
  calc
    ‖x^p-y^p‖ ≤ |x-y| * (p : ℝ)*max |x| |y|^(p-1) := abs_pow_sub_pow_le x y p
    _ ≤ |x-y| * (p : ℝ)*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (p : ℝ)*‖x-y‖ := by rw [Real.norm_eq_abs]; ring

noncomputable def radialTruncatedNonlinearity (p : ℕ) (lo hi : ℝ)
    (V : ℝ → ℝ) (r x : ℝ) : ℝ :=
  (radialAmplitudeClamp lo hi x)^p-V r*radialAmplitudeClamp lo hi x

theorem continuous_radialTruncatedNonlinearity (p : ℕ) (lo hi : ℝ)
    (V : ℝ → ℝ) (hV : Continuous V) :
    Continuous (Function.uncurry (radialTruncatedNonlinearity p lo hi V)) := by
  unfold radialTruncatedNonlinearity radialAmplitudeClamp Function.uncurry
  fun_prop

theorem radialTruncatedNonlinearity_bound (p : ℕ) (lo hi C : ℝ)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) (hC : 0 ≤ C)
    (V : ℝ → ℝ) (r : ℝ) (hV : ‖V r‖ ≤ C) (x : ℝ) :
    ‖radialTruncatedNonlinearity p lo hi V r x‖ ≤ 1+C := by
  have hx := radialAmplitudeClamp_mem lo hi x hlohi
  have hx0 := hlo.trans hx.1
  have hx1 := hx.2.trans hhi
  have hnorm : ‖radialAmplitudeClamp lo hi x‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx0] using hx1
  calc
    ‖radialTruncatedNonlinearity p lo hi V r x‖ ≤
        ‖(radialAmplitudeClamp lo hi x)^p‖+‖V r*radialAmplitudeClamp lo hi x‖ :=
      norm_sub_le _ _
    _ ≤ 1+C := by
      rw [norm_pow,norm_mul]
      exact add_le_add (pow_le_one₀ (norm_nonneg _) hnorm)
        ((mul_le_mul hV hnorm (norm_nonneg _) hC).trans_eq (mul_one C))

theorem radialTruncatedNonlinearity_lipschitz (p : ℕ) (lo hi C : ℝ)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) (hC : 0 ≤ C)
    (V : ℝ → ℝ) (r : ℝ) (hV : ‖V r‖ ≤ C) (x y : ℝ) :
    ‖radialTruncatedNonlinearity p lo hi V r x-
        radialTruncatedNonlinearity p lo hi V r y‖ ≤ ((p : ℝ)+C)*‖x-y‖ := by
  have hx := radialAmplitudeClamp_mem lo hi x hlohi
  have hy := radialAmplitudeClamp_mem lo hi y hlohi
  have hdiff : ‖radialAmplitudeClamp lo hi x-radialAmplitudeClamp lo hi y‖ ≤ ‖x-y‖ := by
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using
      (radialAmplitudeClamp_lipschitz lo hi).dist_le_mul x y
  have hp := unit_interval_power_difference p _ _
    ⟨hlo.trans hx.1,hx.2.trans hhi⟩ ⟨hlo.trans hy.1,hy.2.trans hhi⟩
  unfold radialTruncatedNonlinearity
  rw [show (radialAmplitudeClamp lo hi x)^p-V r*radialAmplitudeClamp lo hi x-
      ((radialAmplitudeClamp lo hi y)^p-V r*radialAmplitudeClamp lo hi y)=
      ((radialAmplitudeClamp lo hi x)^p-(radialAmplitudeClamp lo hi y)^p)-
        V r*(radialAmplitudeClamp lo hi x-radialAmplitudeClamp lo hi y) by ring]
  calc
    _ ≤ ‖(radialAmplitudeClamp lo hi x)^p-(radialAmplitudeClamp lo hi y)^p‖+
        ‖V r*(radialAmplitudeClamp lo hi x-radialAmplitudeClamp lo hi y)‖ := norm_sub_le _ _
    _ ≤ (p : ℝ)*‖x-y‖+C*‖x-y‖ := by
      rw [norm_mul]
      exact add_le_add (hp.trans (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg _)))
        (mul_le_mul hV hdiff (norm_nonneg _) hC)
    _ = _ := by ring

end DefocusingNLS

end OAI
