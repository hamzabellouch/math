import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! The integrating-factor formula for the scalar forced heat equation,
including a distributional initial value represented by a one-sided limit. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

theorem heat_forced_scalar_formula (f r : ℝ → ℝ) (rate a t : ℝ) (ht : 0 < t)
    (hr : ContinuousOn r (Icc 0 t))
    (h0 : Tendsto f (𝓝[>] 0) (𝓝 a))
    (hd : ∀ s > 0, HasDerivAt f (r s - rate * f s) s) :
    f t = Real.exp (-rate * t) * a +
      ∫ s in (0 : ℝ)..t, Real.exp (-rate * (t - s)) * r s := by
  have hprod (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun s => Real.exp (rate * s) * f s) (Real.exp (rate * s) * r s) s := by
    have he := ((hasDerivAt_id s).const_mul rate).exp
    simp only [id_eq, mul_one] at he
    have h := he.mul (hd s hs)
    convert h using 1; ring
  have hi : IntervalIntegrable (fun s => Real.exp (rate * s) * r s) volume 0 t :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hr).intervalIntegrable_of_Icc ht.le
  have ha : Tendsto (fun s => Real.exp (rate * s) * f s) (𝓝[>] 0) (𝓝 a) := by
    have he : ContinuousAt (fun s : ℝ => Real.exp (rate * s)) 0 := by fun_prop
    simpa only [mul_zero, Real.exp_zero, one_mul] using
      (he.tendsto.mono_left nhdsWithin_le_nhds).mul h0
  have hb : Tendsto (fun s => Real.exp (rate * s) * f s) (𝓝[<] t)
      (𝓝 (Real.exp (rate * t) * f t)) :=
    (hprod t ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht
    (fun s hs => hprod s hs.1) hi ha hb
  have hexp : Real.exp (-rate * t) * Real.exp (rate * t) = 1 := by
    rw [← Real.exp_add]
    rw [show -rate * t + rate * t = 0 by ring, Real.exp_zero]
  have heq : (fun s => Real.exp (-rate * (t - s)) * r s) =
      (fun s => Real.exp (-rate * t) * (Real.exp (rate * s) * r s)) := by
    funext s
    rw [show -rate * (t - s) = -rate * t + rate * s by ring, Real.exp_add]
    ring
  rw [heq, intervalIntegral.integral_const_mul, hFTC]
  calc
    f t = (Real.exp (-rate * t) * Real.exp (rate * t)) * f t := by rw [hexp, one_mul]
    _ = _ := by ring

end
end PositiveEinsteinFour.Geometry

end OAI
