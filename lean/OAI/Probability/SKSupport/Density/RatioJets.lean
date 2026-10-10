import Mathlib
import OAI.Probability.SKSupport.Parabolic.ForwardConstruction
import OAI.Probability.SKSupport.Moments.BurgersJets

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def ratioWronskian (r s : ℝ → ℝ → ℝ) (t x : ℝ) :=
  r t x*deriv (s t) x-s t x*deriv (r t) x

def ratioWronskianRate (r s : ℝ → ℝ → ℝ) (t x : ℝ) :=
  -burgersRate r t x*deriv (s t) x+r t x*deriv (scoreRate s t) x-
    scoreRate s t x*deriv (r t) x+s t x*deriv (burgersRate r t) x

lemma burgersRate_spatial_deriv {r : ℝ → ℝ → ℝ} {t : ℝ}
    (hr : ContDiff ℝ ∞ (r t)) (x : ℝ) :
    deriv (burgersRate r t) x=(1/2:ℝ)*iteratedDeriv 3 (r t) x+
      (deriv (r t) x)^2+r t x*iteratedDeriv 2 (r t) x := by
  have hd := ((hasDerivAt_spatialJet hr 2 x).const_mul (1/2:ℝ)).add
    ((hasDerivAt_spatialJet hr 0 x).mul (hasDerivAt_spatialJet hr 1 x))
  have hd' : HasDerivAt (burgersRate r t) ((1/2:ℝ)*iteratedDeriv 3 (r t) x+
      (deriv (r t) x)^2+r t x*iteratedDeriv 2 (r t) x) x := by
    convert hd using 1 <;> first | rfl | ((try funext y); simp only [burgersRate,Pi.add_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  exact hd'.deriv

lemma ratioWronskian_spatial {r s : ℝ → ℝ → ℝ} {t : ℝ}
    (hr : ContDiff ℝ ∞ (r t)) (hs : ContDiff ℝ ∞ (s t)) (x : ℝ) :
    HasDerivAt (ratioWronskian r s t)
      (r t x*iteratedDeriv 2 (s t) x-s t x*iteratedDeriv 2 (r t) x) x := by
  convert ((hasDerivAt_spatialJet hr 0 x).mul (hasDerivAt_spatialJet hs 1 x)).sub
    ((hasDerivAt_spatialJet hs 0 x).mul (hasDerivAt_spatialJet hr 1 x)) using 1 <;>
    first | rfl | ((try funext y); simp only [ratioWronskian,Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)

lemma ratioWronskian_second {r s : ℝ → ℝ → ℝ} {t : ℝ}
    (hr : ContDiff ℝ ∞ (r t)) (hs : ContDiff ℝ ∞ (s t)) (x : ℝ) :
    HasDerivAt (deriv (ratioWronskian r s t))
      (deriv (r t) x*iteratedDeriv 2 (s t) x+r t x*iteratedDeriv 3 (s t) x-
        deriv (s t) x*iteratedDeriv 2 (r t) x-s t x*iteratedDeriv 3 (r t) x) x := by
  have he : deriv (ratioWronskian r s t)=fun y =>
      r t y*iteratedDeriv 2 (s t) y-s t y*iteratedDeriv 2 (r t) y :=
    funext (fun y => (ratioWronskian_spatial hr hs y).deriv)
  rw [he]
  convert ((hasDerivAt_spatialJet hr 0 x).mul (hasDerivAt_spatialJet hs 2 x)).sub
    ((hasDerivAt_spatialJet hs 0 x).mul (hasDerivAt_spatialJet hr 2 x)) using 1 <;>
    first | rfl | (simp only [iteratedDeriv_succ,iteratedDeriv_zero]; ring)

lemma ratioWronskian_time {r s : ℝ → ℝ → ℝ} (hs : SmoothForward s) {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hrt : HasDerivAt (fun u => r u x) (-burgersRate r t x) t)
    (hvt : HasDerivAt (fun u => deriv (r u) x) (-deriv (burgersRate r t) x) t) :
    HasDerivAt (fun u => ratioWronskian r s u x) (ratioWronskianRate r s t x) t := by
  convert (hrt.mul (hs.time_derivative 1 t ht x)).sub
    ((hs.time_derivative 0 t ht x).mul hvt) using 1 <;>
    first | rfl | ((try funext y); simp only [ratioWronskian,ratioWronskianRate,Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)

lemma ratioWronskian_equation {r s : ℝ → ℝ → ℝ} (hs : SmoothForward s) {t : ℝ}
    (hr : ContDiff ℝ ∞ (r t)) (x : ℝ) (hne : r t x ≠ 0) :
    ratioWronskianRate r s t x-(1/2:ℝ)*iteratedDeriv 2 (ratioWronskian r s t) x+
      (deriv (r t) x/r t x)*deriv (ratioWronskian r s t) x+
      (deriv (r t) x+deriv (s t) x)*ratioWronskian r s t x =
      r t x*s t x*(2*backwardWronskian r t x/(r t x)^2-
        iteratedDeriv 2 (r t) x-iteratedDeriv 2 (s t) x) := by
  have hxx : iteratedDeriv 2 (ratioWronskian r s t) x =
      deriv (r t) x*iteratedDeriv 2 (s t) x+r t x*iteratedDeriv 3 (s t) x-
        deriv (s t) x*iteratedDeriv 2 (r t) x-s t x*iteratedDeriv 3 (r t) x := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using (ratioWronskian_second hr (hs.family.smooth t) x).deriv
  rw [hxx,(ratioWronskian_spatial hr (hs.family.smooth t) x).deriv]
  simp only [ratioWronskianRate,ratioWronskian,backwardWronskian,
    burgersRate_spatial_deriv hr,hs.rate_deriv,burgersRate,scoreRate]
  field_simp [hne]
  ring

lemma tangent_bound_of_concave_odd {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hzero : r 0=0) (hw : ∀ x, 0 < x → iteratedDeriv 2 r x ≤ 0)
    {x : ℝ} (hx : 0 ≤ x) : x*deriv r x ≤ r x := by
  let F (x : ℝ) := r x-x*deriv r x
  have hd (x : ℝ) : HasDerivAt F (-x*iteratedDeriv 2 r x) x := by
    convert (hasDerivAt_spatialJet hr 0 x).sub ((hasDerivAt_id x).mul (hasDerivAt_spatialJet hr 1 x)) using 1 <;>
      first | rfl | ((try funext y); simp only [F,id_eq,iteratedDeriv_zero,iteratedDeriv_succ,Pi.mul_apply,Pi.sub_apply] <;> ring)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (D := Ici (0:ℝ)) (convex_Ici (0:ℝ))
    (show ContinuousOn F (Ici (0:ℝ)) from (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn)
    (fun x _ => (hd x).hasDerivWithinAt) (fun x hx => ?_)
  · have hh := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
    dsimp [F] at hh
    rw [hzero,zero_mul,sub_zero] at hh
    linarith
  · have hxp : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hxp.le) (hw x hxp)

end ZeroTemperatureSK.Heat

end
end

end OAI
