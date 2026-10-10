import OAI.NumberTheory.CubicMoment.Estimates.GaussianMellin

namespace OAI

/-! The trace Fourier Riesz identity at the two exponents needed for cubing. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set
namespace CubicFirstMoment

/-- The Riesz identity before dividing by Gamma(2/3). -/
theorem riesz_trace_identity (F : 𝓢(ℂ,ℂ)) :
    (Real.Gamma (2/3:ℝ):ℂ)*
      (∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*traceFourier F z) =
      ((Real.pi*(4*Real.pi^2)^(-(1/3:ℝ))*Real.Gamma (1/3:ℝ):ℝ):ℂ)*
        (∫ z : ℂ, ((‖z‖^(-(2/3:ℝ)):ℝ):ℂ)*F z) := by
  let H (v : ℝ) := ∫ z : ℂ, F z*Complex.exp (-(v:ℂ)*‖z‖^2)
  let c : ℝ := 4*Real.pi^2
  have hc : 0 < c := by dsimp [c]; positivity
  have hstart := gaussian_mellin_identity (traceFourierSchwartz F)
    (a := 2/3) (by norm_num) (by norm_num)
  norm_num only at hstart
  simp only [traceFourierSchwartz_apply] at hstart
  have hfinish := gaussian_mellin_identity F (a := 1/3) (by norm_num) (by norm_num)
  norm_num only at hfinish
  have hheat (t : ℝ) (ht : 0 < t) :
      (∫ y : ℂ, traceFourier F y*Complex.exp (-(t:ℂ)*‖y‖^2)) =
        ((Real.pi/t:ℝ):ℂ)*H (c/t) := by
    rw [integral_traceFourier_gaussian F F.integrable ht]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [H,c]
    congr 1
    congr 1
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hpower (t : ℝ) (ht : 0 < t) :
      ((t^(-(1/3:ℝ)):ℝ):ℂ)*((Real.pi/t:ℝ):ℂ) =
        (Real.pi:ℂ)*((t^(-(4/3:ℝ)):ℝ):ℂ) := by
    have he : t^(-(1/3:ℝ))/t = t^(-(4/3:ℝ)) := by
      nth_rw 2 [← Real.rpow_one t]
      rw [← Real.rpow_sub ht]
      norm_num
    have hr : t^(-(1/3:ℝ))*(Real.pi/t) = Real.pi*t^(-(4/3:ℝ)) := by
      calc
        _ = Real.pi*(t^(-(1/3:ℝ))/t) := by ring
        _ = _ := by rw [he]
    exact_mod_cast hr
  rw [hstart]
  calc
    _ = (Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), (t^(-(4/3:ℝ)):ℝ)*H (c/t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [hheat t ht,← mul_assoc,hpower t ht,mul_assoc]
    _ = (Real.pi:ℂ)*((c^(-(1/3:ℝ)):ℝ):ℂ)*
        (∫ v in Ioi (0:ℝ), (v^(-(2/3:ℝ)):ℝ)*H v) := by
      have hi := inverse_mellin_change H (2/3) hc
      norm_num only at hi
      rw [hi,mul_assoc]
    _ = _ := by
      rw [← hfinish]
      dsimp only [c]
      push_cast
      ring

end CubicFirstMoment

end

end OAI
