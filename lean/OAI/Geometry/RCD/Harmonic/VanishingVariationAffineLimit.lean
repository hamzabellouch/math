import OAI.Geometry.RCD.Metric.DerivativeValueCompactness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! # Affine limits from locally vanishing integrated second variation -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem integrated_derivative_oscillation {f g : ℝ → ℝ} {a b C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x ∈ Icc a b, |g x| ≤ C)
    (hint : ∀ u v, a ≤ u → u ≤ v → v ≤ b →
      (∫ t in u..v, g t) = deriv f v-deriv f u)
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    |deriv f u-deriv f v| ≤ C*(b-a) := by
  have hord (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      |deriv f y-deriv f x| ≤ C*(b-a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x) (b := y) (f := g) (C := C) (fun t ht => by
        rw [uIoc_of_le hxy] at ht
        simpa only [Real.norm_eq_abs] using hbound t ⟨hx.1.trans ht.1.le,ht.2.trans hy.2⟩)
    rw [hint x y hx.1 hxy hy.2, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hx.1,hy.2]) hC)
  rcases le_total u v with huv | hvu
  · simpa only [abs_sub_comm] using hord u v hu hv huv
  · exact hord v u hv hu hvu

theorem chord_error_le_of_derivative_oscillation {f : ℝ → ℝ} {a b C x : ℝ}
    (hab : a < b) (hC : 0 ≤ C) (hx : x ∈ Icc a b)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hosc : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |deriv f u-deriv f v| ≤ C*(b-a)) :
    |f x-f a-((f b-f a)/(b-a))*(x-a)| ≤ C*(b-a)^2 := by
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f hab
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t ⟨ht.1.le,ht.2.le⟩).differentiableWithinAt)
  let m := (f b-f a)/(b-a)
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun z => f z-m*(z-a)) (deriv f t-m) t := by
    simpa only [Pi.sub_apply,id_eq,sub_zero,mul_one] using!
      (hf t ht).hasDerivAt.sub (((hasDerivAt_id t).sub_const a).const_mul m)
  have hbd (t : ℝ) (ht : t ∈ Icc a b) : ‖deriv f t-m‖ ≤ C*(b-a) := by
    simpa only [Real.norm_eq_abs,he,m] using hosc t ht c ⟨hc.1.le,hc.2.le⟩
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hbd (convex_Icc a b) (left_mem_Icc.mpr hab.le) hx
  simp only [sub_self,mul_zero,sub_zero,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hx.1)] at hh
  have heq : f x-m*(x-a)-f a = f x-f a-m*(x-a) := by ring
  rw [heq] at hh
  apply hh.trans
  calc
    C*(b-a)*(x-a) ≤ C*(b-a)*(b-a) := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hx.2 a) (mul_nonneg hC (sub_nonneg.mpr hab.le))
    _ = C*(b-a)^2 := by ring

theorem chord_eq_of_vanishing_second_variation
    (F G : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ k t, t ∈ Ioo (0:ℝ) 1 → DifferentiableAt ℝ (F k) t)
    (hint : ∀ k a b, 0 < a → a ≤ b → b < 1 →
      (∫ t in a..b, G k t) = deriv (F k) b-deriv (F k) a)
    (hG : ∀ a b, 0 < a → a ≤ b → b < 1 →
      TendstoUniformlyOn G (fun _ => 0) atTop (Icc a b))
    (hval : ∀ t ∈ Ioo (0:ℝ) 1, Tendsto (fun k => F k t) atTop (𝓝 (f t)))
    {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hx : x ∈ Icc a b) :
    (b-a)*(f x-f a) = (x-a)*(f b-f a) := by
  have hwin (t : ℝ) (ht : t ∈ Icc a b) : t ∈ Ioo (0:ℝ) 1 :=
    ⟨ha.trans_le ht.1,ht.2.trans_lt hb⟩
  have hslope := (((hval b ⟨ha.trans hab,hb⟩).sub
    (hval a ⟨ha,hab.trans hb⟩)).div_const (b-a)).mul_const (x-a)
  have hlim := (((hval x (hwin x hx)).sub (hval a ⟨ha,hab.trans hb⟩)).sub hslope).abs
  have hzero : |f x-f a-((f b-f a)/(b-a))*(x-a)| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro e he
    let δ := e/((b-a)^2+1)
    have hδ : 0 < δ := div_pos he (by positivity)
    have hsmall : ∀ᶠ k in atTop,
        |F k x-F k a-((F k b-F k a)/(b-a))*(x-a)| ≤ δ*(b-a)^2 := by
      filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hG a b ha hab.le hb)) δ hδ] with k hk
      apply chord_error_le_of_derivative_oscillation hab hδ.le hx (fun t ht => hF k t (hwin t ht))
      intro u hu v hv
      apply integrated_derivative_oscillation (g := G k) hδ.le _ _ hu hv
      · intro t ht
        have hh := hk t ht
        simpa only [dist_zero_left,Real.norm_eq_abs] using hh.le
      · intro u v hau huv hvb
        exact hint k u v (ha.trans_le hau) huv (hvb.trans_lt hb)
    have hle := le_of_tendsto hlim hsmall
    have heq : δ*((b-a)^2+1)=e := div_mul_cancel₀ e (by positivity)
    dsimp only [δ] at heq
    change |f x-f a-((f b-f a)/(b-a))*(x-a)| ≤ 0+e
    have hstrict : δ*(b-a)^2 ≤ e := by
      change δ*((b-a)^2+1)=e at heq
      nlinarith
    simpa only [zero_add] using hle.trans hstrict
  have he := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  have hne : b-a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  field_simp [hne] at he
  nlinarith only [he]

theorem affine_of_vanishing_second_variation
    (F G : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ k t, t ∈ Ioo (0:ℝ) 1 → DifferentiableAt ℝ (F k) t)
    (hint : ∀ k a b, 0 < a → a ≤ b → b < 1 →
      (∫ t in a..b, G k t) = deriv (F k) b-deriv (F k) a)
    (hG : ∀ a b, 0 < a → a ≤ b → b < 1 →
      TendstoUniformlyOn G (fun _ => 0) atTop (Icc a b))
    (hval : ∀ t ∈ Ioo (0:ℝ) 1, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    ∃ α β : ℝ, ∀ t ∈ Ioo (0:ℝ) 1, f t=α*t+β := by
  refine ⟨3*(f (2/3)-f (1/3)),2*f (1/3)-f (2/3),fun t ht => ?_⟩
  rcases le_total t (1/3) with hleft | hright
  · have hh := chord_eq_of_vanishing_second_variation F G f hF hint hG hval
      ht.1 (show t < 2/3 by linarith) (by norm_num : (2/3:ℝ)<1)
      (show (1/3:ℝ) ∈ Icc t (2/3) from ⟨hleft,by norm_num⟩)
    nlinarith only [hh]
  · rcases le_total t (2/3) with hmid | hlast
    · have hh := chord_eq_of_vanishing_second_variation F G f hF hint hG hval
        (by norm_num : (0:ℝ)<1/3) (by norm_num : (1/3:ℝ)<2/3)
        (by norm_num : (2/3:ℝ)<1) ⟨hright,hmid⟩
      nlinarith only [hh]
    · have hh := chord_eq_of_vanishing_second_variation F G f hF hint hG hval
        (by norm_num : (0:ℝ)<1/3) (show (1/3:ℝ)<t by linarith) ht.2
        (show (2/3:ℝ) ∈ Icc (1/3) t from ⟨by norm_num,hlast⟩)
      nlinarith only [hh]

end RegularPointCoordinates

end

end OAI
