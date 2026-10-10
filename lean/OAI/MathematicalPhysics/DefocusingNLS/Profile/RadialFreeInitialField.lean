import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

/-! The exact first-order system for the short free radial initial-value problem. -/

open Set
namespace DefocusingNLS

noncomputable def radialFreeCoefficient (r : ℝ) : ℂ :=
  ((11/r : ℝ) : ℂ)+Complex.I*((r/2 : ℝ) : ℂ)

noncomputable def radialFreeField (b r : ℝ) (x : ℂ × ℂ) : ℂ × ℂ :=
  (x.2,-radialFreeCoefficient r*x.2-(b : ℂ)*x.1)

theorem radialFreeCoefficient_norm (r : ℝ) (hr : r ∈ Icc (3 : ℝ) (10/3)) :
    ‖radialFreeCoefficient r‖ ≤ 6 := by
  have hr0 : 0 < r := by linarith [hr.1]
  have hdiv : 11/r ≤ (11/3 : ℝ) := (div_le_iff₀ hr0).mpr (by linarith [hr.1])
  have hn := norm_add_le (((11/r : ℝ) : ℂ)) (Complex.I*((r/2 : ℝ) : ℂ))
  rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (div_pos (by norm_num) hr0),
    abs_of_pos (div_pos hr0 (by norm_num))] at hn
  exact hn.trans (by linarith [hr.2])

theorem radialFreeField_norm (b r : ℝ) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hr : r ∈ Icc (3 : ℝ) (10/3)) (x : ℂ × ℂ) :
    ‖radialFreeField b r x‖ ≤ 7*‖x‖ := by
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hbn : ‖(b : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb0]
    linarith [hb.2]
  have hs : ‖-radialFreeCoefficient r*x.2-(b : ℂ)*x.1‖ ≤ 7*‖x‖ := by
    calc
      _ ≤ ‖-radialFreeCoefficient r*x.2‖+‖(b : ℂ)*x.1‖ := norm_sub_le _ _
      _ = ‖radialFreeCoefficient r‖*‖x.2‖+‖(b : ℂ)‖*‖x.1‖ := by rw [norm_mul,norm_neg,norm_mul]
      _ ≤ 6*‖x.2‖+1*‖x.1‖ := by gcongr; exact radialFreeCoefficient_norm r hr
      _ ≤ 6*‖x‖+1*‖x‖ := by gcongr; exacts [norm_snd_le x,norm_fst_le x]
      _ = 7*‖x‖ := by ring
  change max ‖x.2‖ ‖-radialFreeCoefficient r*x.2-(b : ℂ)*x.1‖ ≤ _
  exact max_le ((norm_snd_le x).trans (by nlinarith [norm_nonneg x])) hs

theorem radialFreeField_sub (b r : ℝ) (x y : ℂ × ℂ) :
    radialFreeField b r (x-y)=radialFreeField b r x-radialFreeField b r y := by
  apply Prod.ext
  · rfl
  · change -radialFreeCoefficient r*(x.2-y.2)-(b : ℂ)*(x.1-y.1)=
      (-radialFreeCoefficient r*x.2-(b : ℂ)*x.1)-(-radialFreeCoefficient r*y.2-(b : ℂ)*y.1)
    ring

theorem radialFreeField_lipschitz (b r : ℝ) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hr : r ∈ Icc (3 : ℝ) (10/3)) : LipschitzWith 7 (radialFreeField b r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  rw [← radialFreeField_sub]
  exact radialFreeField_norm b r hb hr (x-y)

theorem radialFreeField_continuousOn (b l u : ℝ) (hl : 0 < l) (x : ℂ × ℂ) :
    ContinuousOn (fun r => radialFreeField b r x) (Icc l u) := by
  have hdiv : ContinuousOn (fun r : ℝ => 11/r) (Icc l u) :=
    continuousOn_const.div continuousOn_id (fun r hr => ne_of_gt (hl.trans_le hr.1))
  have hc : ContinuousOn radialFreeCoefficient (Icc l u) :=
    (Complex.continuous_ofReal.comp_continuousOn hdiv).add
      (continuousOn_const.mul ((Complex.continuous_ofReal.comp (continuous_id.div_const 2)).continuousOn))
  exact continuousOn_const.prodMk ((hc.neg.mul continuousOn_const).sub continuousOn_const)

end DefocusingNLS

end OAI
