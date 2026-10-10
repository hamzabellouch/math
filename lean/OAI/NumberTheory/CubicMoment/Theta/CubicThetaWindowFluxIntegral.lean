import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWindowFlux
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroObservable

namespace OAI

/-! Exact boundary evaluation of the constant theta-window observation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHighWindowFluxDensity (v : ℝ) : ℂ :=
  (v:ℂ)^(-7/3:ℂ)*cubicThetaHighWindowForcing (4/3) v

lemma cubicThetaHighWindowFluxDensity_continuousOn :
    ContinuousOn cubicThetaHighWindowFluxDensity (Icc (2:ℝ) 4) := by
  intro v hv
  exact (((cubicThetaHeightPower_analytic (-7/3) (by linarith [hv.1])).continuousAt).mul
    (cubicThetaHighWindowForcing_continuous (4/3)).continuousAt).continuousWithinAt

lemma cubicThetaHighWindowFluxDensity_integral :
    (∫ v in Ioi (2:ℝ),cubicThetaHighWindowFluxDensity v)=2/3 := by
  have hi : IntervalIntegrable cubicThetaHighWindowFluxDensity volume 2 4 :=
    cubicThetaHighWindowFluxDensity_continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hcont : ContinuousOn cubicThetaWindowFlux (Icc (2:ℝ) 4) := by
    intro v hv
    exact (cubicThetaWindowFlux_hasDerivAt (by linarith [hv.1])).continuousAt.continuousWithinAt
  have hd (v : ℝ) (hv : v∈Ioo (2:ℝ) 4) :
      HasDerivAt cubicThetaWindowFlux (-cubicThetaHighWindowFluxDensity v) v := by
    have hf := cubicThetaWindowFlux_hasDerivAt (by linarith [hv.1])
    convert hf using 1
    rw [cubicThetaHighWindowFluxDensity,cubicThetaHighWindowForcing,
      cubicThetaIncomingForcing_zero (4/3) (Or.inr hv.1)]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (2:ℝ)≤4) hcont hd hi.neg
  rw [intervalIntegral.integral_neg,cubicThetaWindowFlux_high (by norm_num),
    cubicThetaWindowFlux_two] at he
  have he' : (∫ v in (2:ℝ)..4,cubicThetaHighWindowFluxDensity v)=2/3 := by
    linear_combination -he
  rw [intervalIntegral.integral_of_le (by norm_num)] at he'
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (2:ℝ) 4⊆Ioi 2 from fun _ hv => hv.1)]
  · exact he'
  · intro v hv
    have hv4 : 4≤v := by
      have hn := hv.2
      simp only [mem_Ioc,not_and] at hn
      exact (lt_of_not_ge (hn hv.1)).le
    rw [cubicThetaHighWindowFluxDensity,cubicThetaHighWindowForcing_high _ hv4,mul_zero]

lemma cubicThetaHighWindowZeroRadial_integrand {v : ℝ} (hv : 0<v) :
    star (cubicThetaHighWindowForcing (4/3) v)*(v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3=
      star (cubicThetaHighWindowFluxDensity v) := by
  have hn : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3=(v:ℂ)^(-7/3:ℂ) := by
    rw [←Complex.cpow_ofNat,←Complex.cpow_sub _ _ hn]
    congr 1
    ring
  have hs : star ((v:ℂ)^(-7/3:ℂ))=(v:ℂ)^(-7/3:ℂ) := by
    have hr := Complex.ofReal_cpow hv.le (-7/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat] at hr
    norm_num only [neg_div] at hr ⊢
    rw [←hr]
    exact Complex.conj_ofReal _
  rw [cubicThetaHighWindowFluxDensity,star_mul,hs]
  calc
    _ = star (cubicThetaHighWindowForcing (4/3) v)*
      ((v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3) := by ring
    _ = _ := by rw [hp]

theorem cubicThetaHighWindow_zero_radial :
    cubicThetaZeroRadialTest (cubicThetaHighWindowWeight (4/3)) (4/3)=2/3 := by
  unfold cubicThetaZeroRadialTest
  have he : (∫ v in Ioi (2:ℝ),star (cubicThetaHighWindowForcing (4/3) v)*
      (v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3)=
      ∫ v in Ioi (2:ℝ),star (cubicThetaHighWindowFluxDensity v) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact cubicThetaHighWindowZeroRadial_integrand (lt_trans (by norm_num) hv)
  change (∫ v in Ioi (2:ℝ),star (cubicThetaHighWindowForcing (4/3) v)*
    (v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3)=_
  rw [he]
  change (∫ v in Ioi (2:ℝ),(starRingEnd ℂ) (cubicThetaHighWindowFluxDensity v))=_
  rw [integral_conj,cubicThetaHighWindowFluxDensity_integral]
  norm_num [starRingEnd_apply,Complex.star_def]

end CubicFirstMoment

end

end OAI
