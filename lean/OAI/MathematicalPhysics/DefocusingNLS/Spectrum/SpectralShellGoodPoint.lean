import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinNormBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Select bounded Cauchy data in the first half of the shell from its
integrated energy and the coercive local Robin relation. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_interval_energy_point (a b K : ℝ) (hab : a < b)
    (e : ℝ → ℝ) (he : ContinuousOn e (Icc a b)) (hbound : (∫ r in a..b, e r) ≤ K) :
    ∃ r ∈ Icc a b, e r ≤ K/(b-a) := by
  obtain ⟨r,hr,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) he
  refine ⟨r,hr,?_⟩
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (intervalIntegrable_const (c := e r)) (he.intervalIntegrable_of_Icc hab.le) (fun x hx => hmin hx)
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by nlinarith)

theorem spectral_shell_good_point (a b K mu : ℝ) (hab : a < b) (hmu : 0 ≤ mu)
    (q : ℝ → (ℂ × ℂ) × (ℂ × ℂ)) (hq : ContinuousOn q (Icc a b))
    (hrobin : ∀ r ∈ Icc a b,
      mu*(‖(q r).1.1‖+‖(q r).2.1‖) ≤ 2*(‖(q r).1.2‖+‖(q r).2.2‖))
    (hbound : (∫ r in a..b, ‖(q r).1.2‖^2+‖(q r).2.2‖^2) ≤ K) :
    ∃ r ∈ Icc a b, ‖(q r).1.2‖^2+‖(q r).2.2‖^2 ≤ K/(b-a) ∧
      mu^2*(‖(q r).1.1‖^2+‖(q r).2.1‖^2) ≤ 8*(K/(b-a)) := by
  obtain ⟨r,hr,hb⟩ := spectral_interval_energy_point a b K hab
    (fun r => ‖(q r).1.2‖^2+‖(q r).2.2‖^2)
    ((hq.fst.snd.norm.pow 2).add (hq.snd.snd.norm.pow 2)) hbound
  refine ⟨r,hr,hb,?_⟩
  have hc := hrobin r hr
  have hs := pow_le_pow_left₀ (mul_nonneg hmu (by positivity)) hc 2
  have hcross := sq_nonneg (‖(q r).1.2‖-‖(q r).2.2‖)
  have hp : 0 ≤ mu^2*‖(q r).1.1‖*‖(q r).2.1‖ := by positivity
  nlinarith only [hs,hcross,hp,hb]

end DefocusingNLS

end OAI
