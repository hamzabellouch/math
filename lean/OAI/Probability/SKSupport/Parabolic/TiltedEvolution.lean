import Mathlib
import OAI.Probability.SKSupport.Regularity.BoundedSmoothFamily

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma varianceTilted_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) : BoundedSmoothFamily (fun t => varianceTilted c t f g) := by
  have he (t : ℝ) : varianceTilted c t f g=tiltedMean c (Real.toNNReal t) f g :=
    funext (varianceTilted_eq_tiltedMean hf.smooth.continuous.measurable hg.smooth.continuous.measurable c t)
  refine ⟨?_,fun t => by rw [he];exact boundedSmooth_tiltedMean hf hLip hg hc _,?_⟩
  · exact (measurable_varianceHeat_family (F := fun _ y => g y*Real.exp (c*f y))
      (hg.smooth.continuous.measurable.comp measurable_snd |>.mul
        ((measurable_const.mul (hf.smooth.continuous.measurable.comp measurable_snd)).exp)) measurable_id).div
      (measurable_varianceHeat_family (F := fun _ y => Real.exp (c*f y))
        ((measurable_const.mul (hf.smooth.continuous.measurable.comp measurable_snd)).exp) measurable_id)
  · intro n
    obtain ⟨C,hC⟩ := uniform_tiltedMean_bounds hf hLip hg hc n
    exact ⟨C,fun t x => by rw [he];exact hC _ x⟩

lemma varianceTilted_continuousOn {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => varianceTilted c p.1 f g p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  obtain ⟨L,hL⟩ := varianceTilted_joint_bound hf hLip hg hc
  apply continuousOn_of_joint_bound (F := fun t => varianceTilted c t f g) (L := L)
  intro t ht s hs x y
  exact hL t ht.1 s hs.1 x y

lemma second_deriv_mul {F G : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (x : ℝ) :
    deriv (deriv (fun y => F y*G y)) x =
      deriv (deriv F) x*G x+2*deriv F x*deriv G x+F x*deriv (deriv G) x := by
  have he : deriv (fun y => F y*G y)=fun y => deriv F y*G y+F y*deriv G y := by
    funext y
    exact (((hF.differentiable (by norm_num)) y).hasDerivAt.mul
      ((hG.differentiable (by norm_num)) y).hasDerivAt).deriv
  rw [he]
  convert (((((show ContDiff ℝ 1 (deriv F) from hF.deriv').differentiable (by norm_num)) x).hasDerivAt.mul
    ((hG.differentiable (by norm_num)) x).hasDerivAt).add
    (((hF.differentiable (by norm_num)) x).hasDerivAt.mul
    (((show ContDiff ℝ 1 (deriv G) from hG.deriv').differentiable (by norm_num)) x).hasDerivAt)).deriv using 1
  ring

lemma quotient_heat_equation {N D : ℝ → ℝ → ℝ} {t : ℝ} {S : Set ℝ}
    (hN : ContDiff ℝ 2 (N t)) (hD : ContDiff ℝ 2 (D t))
    (hne : ∀ x, D t x ≠ 0)
    (hNt : ∀ x, HasDerivWithinAt (fun u => N u x) ((1/2:ℝ)*deriv (deriv (N t)) x) S t)
    (hDt : ∀ x, HasDerivWithinAt (fun u => D u x) ((1/2:ℝ)*deriv (deriv (D t)) x) S t) (x : ℝ) :
    HasDerivWithinAt (fun u => N u x/D u x)
      ((1/2:ℝ)*deriv (deriv (fun y => N t y/D t y)) x+
        (deriv (D t) x/D t x)*deriv (fun y => N t y/D t y) x) S t := by
  let F := fun y => N t y/D t y
  have hF : ContDiff ℝ 2 F := hN.div hD hne
  have he : N t=fun y => F y*D t y := by funext y;dsimp [F];field_simp [hne y]
  have hxx : deriv (deriv (N t)) x=deriv (deriv F) x*D t x+
      2*deriv F x*deriv (D t) x+F x*deriv (deriv (D t)) x := by
    calc
      _ = deriv (deriv (fun y => F y*D t y)) x := congrArg (fun f => deriv (deriv f) x) he
      _ = _ := second_deriv_mul hF hD x
  convert (hNt x).div (hDt x) (hne x) using 1
  rw [hxx]
  dsimp only [F]
  field_simp [hne x]
  ring

lemma varianceTilted_equation {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun u => varianceTilted c u f g x)
      ((1/2:ℝ)*deriv (deriv (varianceTilted c t f g)) x+
        c*deriv (varianceLogHeat c t f) x*deriv (varianceTilted c t f g) x) (Ici 0) t := by
  let N := fun u => varianceHeat u (fun y => g y*Real.exp (c*f y))
  let D := fun u => varianceHeat u (fun y => Real.exp (c*f y))
  have hD (u : ℝ) : ContDiff ℝ ∞ (D u) := by
    have he : D u=semigroup (Real.toNNReal u) (fun y => Real.exp (c*f y)) :=
      funext (varianceHeat_eq_semigroup_toNNReal ((measurable_const.mul hf.smooth.continuous.measurable).exp) u)
    rw [he]
    exact contDiff_semigroup_exp hf hLip hc _
  have hN (u : ℝ) : ContDiff ℝ ∞ (N u) := by
    have he : N u=semigroup (Real.toNNReal u) (fun y => g y*Real.exp (c*f y)) :=
      funext (varianceHeat_eq_semigroup_toNNReal (hg.smooth.continuous.measurable.mul
        ((measurable_const.mul hf.smooth.continuous.measurable).exp)) u)
    rw [he]
    exact contDiff_semigroup_weight_exp hf hLip hg hc _
  have hNt (y : ℝ) : HasDerivWithinAt (fun u => N u y) ((1/2:ℝ)*deriv (deriv (N t)) y) (Ici 0) t :=
    varianceHeat_equation ((hg.smooth.mul (contDiff_const.mul hf.smooth).exp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (by simpa only [iteratedDeriv_zero] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 0)
      (by simpa only [iteratedDeriv_one] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 1)
      (by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 2) ht y
  have hDt (y : ℝ) : HasDerivWithinAt (fun u => D u y) ((1/2:ℝ)*deriv (deriv (D t)) y) (Ici 0) t := by
    convert varianceHeat_equation ((contDiff_const.mul hf.smooth).exp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (exponentialBound_exp hLip c)
      (by simpa only [iteratedDeriv_one] using exponentialBound_exp_iteratedDeriv hf hLip c 1)
      (by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using exponentialBound_exp_iteratedDeriv hf hLip c 2) ht y using 1
  have hratio : deriv (D t) x/D t x=c*deriv (varianceLogHeat c t f) x := by
    rw [deriv_varianceLogHeat_tilted hf hLip hc]
    have hd := hasDerivAt_semigroup_exp (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hLip hc (Real.toNNReal t) x
    have he : D t=semigroup (Real.toNNReal t) (fun y => Real.exp (c*f y)) :=
      funext (varianceHeat_eq_semigroup_toNNReal ((measurable_const.mul hf.smooth.continuous.measurable).exp) t)
    rw [he,hd.deriv,varianceTilted_eq_tiltedMean hf.smooth.continuous.measurable hf.deriv_bounded.smooth.continuous.measurable]
    simp only [tiltedMean,semigroup]
    rw [← mul_div_assoc,← integral_const_mul]
    apply congrArg (fun z : ℝ => z / ∫ y, Real.exp (c*f (x+y)) ∂gaussianReal 0 (Real.toNNReal t))
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hh := quotient_heat_equation ((hN t).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ((hD t).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun y => ne_of_gt (varianceHeat_exp_pos hLip c t y)) hNt hDt x
  rw [hratio] at hh
  exact hh

end ZeroTemperatureSK.Heat

end
end

end OAI
