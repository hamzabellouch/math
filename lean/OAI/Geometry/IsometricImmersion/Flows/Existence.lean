import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
open Set Metric
open scoped NNReal Interval

namespace SmoothLocal.ODE

def curvatureField (k : ℝ → ℝ) (t : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.2, -k t * u.1)

theorem curvatureField_lipschitz {k : ℝ → ℝ} {t : ℝ}
    (hk : |k t| ≤ (1 : ℝ) / 1000) :
    LipschitzWith 1 (curvatureField k t) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  change max ‖u.2 - v.2‖ ‖-k t * u.1 - -k t * v.1‖ ≤ ‖u - v‖
  refine max_le (norm_snd_le (u - v)) ?_
  calc
    ‖-k t * u.1 - -k t * v.1‖ = |k t| * ‖u.1 - v.1‖ := by
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_neg]
    _ ≤ 1 * ‖u.1 - v.1‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ ‖u - v‖ := by simpa using norm_fst_le (u - v)

theorem curvatureField_norm_le {k : ℝ → ℝ} {t : ℝ}
    (hk : |k t| ≤ (1 : ℝ) / 1000) {u : ℝ × ℝ}
    (hu : u ∈ closedBall ((1 : ℝ), (0 : ℝ)) 2) :
    ‖curvatureField k t u‖ ≤ 2 := by
  have hu' : ‖u - ((1 : ℝ), (0 : ℝ))‖ ≤ 2 := by
    simpa only [mem_closedBall, dist_eq_norm] using hu
  have hfst : |u.1 - 1| ≤ 2 := by
    exact (norm_fst_le (u - ((1 : ℝ), (0 : ℝ)))).trans hu'
  have hsnd : ‖u.2‖ ≤ 2 := by
    simpa using (norm_snd_le (u - ((1 : ℝ), (0 : ℝ)))).trans hu'
  have hu1 : |u.1| ≤ 3 := by
    obtain ⟨ha, hb⟩ := abs_le.mp hfst
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  change max ‖u.2‖ ‖-k t * u.1‖ ≤ 2
  refine max_le hsnd ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  have hh := mul_le_mul hk hu1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 1000)
  linarith

theorem exists_curvature_state_on_closed_interval
    (k : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hkcont : ContinuousOn k (Icc (-r) r))
    (hkbound : ∀ t ∈ Icc (-r) r, |k t| ≤ (1 : ℝ) / 1000) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = (1, 0) ∧
      ∀ t ∈ Icc (-r) r,
        HasDerivWithinAt α (curvatureField k t (α t)) (Icc (-r) r) t := by
  let t₀ : Icc (-r) r := ⟨0, by constructor <;> linarith⟩
  have hPL : IsPicardLindelof (curvatureField k) t₀ (1, 0) 2 0 2 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro u _ v _
      exact (curvatureField_lipschitz (hkbound t ht)).dist_le_mul u v
    · intro u _
      exact continuousOn_const.prodMk (hkcont.neg.mul continuousOn_const)
    · intro t ht u hu
      exact curvatureField_norm_le (hkbound t ht) hu
    · change (2 : ℝ) * max (r - 0) (0 - -r) ≤ (2 : ℝ) - 0
      simp only [sub_zero, zero_sub, neg_neg, max_self]
      linarith
  simpa only [t₀] using hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem curvature_integral_bound (k f : ℝ → ℝ) (x F : ℝ)
    (hF : 0 ≤ F)
    (hk : ∀ t ∈ Set.uIoc 0 x, |k t| ≤ (1 : ℝ) / 1000)
    (hf : ∀ t ∈ Set.uIoc 0 x, |f t| ≤ F) :
    |∫ t in 0..x, k t * f t| ≤ ((1 : ℝ) / 1000) * F * |x| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := x) (C := ((1 : ℝ) / 1000) * F)
    (f := fun t => k t * f t) (fun t ht => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hf t ht) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hk t ht) hF))
  simpa only [Real.norm_eq_abs, sub_zero] using h

theorem positive_of_integral_bounds (f F : ℝ)
    (hF : F ≤ 1 + ((1 : ℝ) / 1000) * F)
    (hf : |f - 1| ≤ ((1 : ℝ) / 1000) * F) :
    (998 : ℝ) / 999 ≤ f ∧ f ≤ (1000 : ℝ) / 999 := by
  obtain ⟨ha, hb⟩ := abs_le.mp hf
  constructor <;> linarith

end SmoothLocal.ODE

end

end OAI
