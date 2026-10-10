import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAiryCoefficient
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAiryState
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarHalfLineExistence
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarUniformDependence

namespace OAI

/-! Actual rescaled scalar solutions converge to one Airy solution whenever
their Cauchy data at the left endpoint converge. The equation is inherited
from the original radial equation, rather than assumed for the limit. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurningAiry_cauchy_limit
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (a c R G : ℝ)
    (q : ℕ → ℝ → ℂ × ℂ) (x : ℂ × ℂ)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8 + 2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1)
    (hq : ∀ᶠ n in atTop, Continuous (q n) ∧ ∀ r ∈ Icc R (2*r₀ n),
      HasDerivAt (q n) (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) r : ℂ) +
          Complex.I*(gamma n : ℂ)) (q n r)) r)
    (hinit : Tendsto (fun n =>
      spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) a) atTop (𝓝 x)) :
    ∃ p : ℝ → ℂ × ℂ, Continuous p ∧ p a = x ∧
      (∀ t, a ≤ t → HasDerivAt p (spectralScalarField (-(t : ℂ)) (p t)) t) ∧
      TendstoUniformlyOn
        (fun n => spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n))
        p atTop (Icc a c) := by
  obtain ⟨p,hp,hpa,hpD⟩ := spectralScalar_halfLine_exists a (fun t => -(t : ℂ))
    (by fun_prop) x
  refine ⟨p,hp,hpa,hpD,?_⟩
  have hd := spectralTurningScale_tendsto eta r₀ d hr₀
    (hdata.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2.2⟩))
  let M := max |a| |c|
  have hM : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  have ha : -M ≤ a := (neg_le_neg (le_max_left |a| |c|)).trans (neg_abs_le a)
  have hc : c ≤ M := (le_abs_self c).trans (le_max_right _ _)
  have hstate : ∀ᶠ n in atTop,
      ContinuousOn (spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n)) (Icc a c) ∧
      ∀ t ∈ Icc a c, HasDerivAt
        (spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n))
        (spectralScalarField
          (spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) (-t))
          (spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) t)) t := by
    filter_upwards [hdata,hq,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hr₀.eventually (eventually_ge_atTop (max (R + M) M))] with n hn hqn hd1 hrn
    have hdn : 0 < d n := by
      apply lt_of_le_of_ne hn.2.1
      intro he
      have heq := hn.2.2.2.2.2
      rw [← he] at heq
      norm_num at heq
    refine ⟨(spectralTurningAiryState_continuous _ _ _ _ hqn.1).continuousOn,?_⟩
    intro t ht
    have htM : |t| ≤ M := abs_le.mpr ⟨ha.trans ht.1,ht.2.trans hc⟩
    have hprod : |d n*t| ≤ M := by
      rw [abs_mul,abs_of_nonneg hn.2.1]
      exact (mul_le_mul_of_nonneg_left htM hn.2.1).trans (by nlinarith)
    have hpoint : r₀ n - d n*t ∈ Icc R (2*r₀ n) := by
      have hleft := (le_max_left (R+M) M).trans hrn
      have hright := (le_max_right (R+M) M).trans hrn
      constructor <;> linarith [(abs_le.mp hprod).1,(abs_le.mp hprod).2]
    exact spectralTurningAiryState_hasDerivAt h (b n) (eta n) (omega n) (gamma n)
      (r₀ n) (d n) (Real.sqrt (d n)) t (Real.sqrt_pos.mpr hdn).ne'
      (Real.sq_sqrt hn.2.1) (q n) (hqn.2 _ hpoint)
  apply spectralScalar_uniform_dependence a c
    (fun n t => spectralTurningCoefficient h (b n) (eta n) (omega n)
      (gamma n) (r₀ n) (d n) (-t)) (fun t => -(t : ℂ))
    (fun n => spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n)) p
    (by fun_prop) hp.continuousOn (fun t ht => hpD t ht.1) hstate
    (spectralTurningAiryCoefficient_uniform_limit h b eta omega gamma r₀ d a c G hr₀ hdata)
  simpa only [hpa] using hinit

end DefocusingNLS

end OAI
