import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseIntegral

namespace OAI

/-! A positive lower bound for momentum controls its phase integral. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_phase_of_lower (a b L : ℝ) (hab : a≤b) (hL : 0<L)
    (p : ℝ → ℝ) (hp : ContinuousOn p (Icc a b))
    (hbound : ∀ t ∈ Icc a b, L≤p t) :
    (∫ t in a..b, 1/p t)≤(b-a)/L := by
  have hp0 (t : ℝ) (ht : t ∈ Icc a b) : 0<p t := hL.trans_le (hbound t ht)
  have hi : IntervalIntegrable (fun t => 1/p t) volume a b :=
    (continuousOn_const.div hp (fun t ht => (hp0 t ht).ne')).intervalIntegrable_of_Icc hab
  calc
    _ ≤ ∫ _ in a..b, 1/L := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
      (fun t ht => by gcongr; exact hbound t ht)
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring

end DefocusingNLS

end OAI
