import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralIntegralGronwall

namespace OAI

/-! An integral forcing bound for propagation across a fixed shell. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_forced_gronwall (a b K : ℝ) (hab : a ≤ b) (hK : 0 ≤ K)
    (y dy e : ℝ → ℝ) (hy : ContinuousOn y (Icc a b))
    (hdy : ContinuousOn dy (Icc a b)) (he : ContinuousOn e (Icc a b))
    (he0 : ∀ r ∈ Icc a b, 0 ≤ e r)
    (hD : ∀ r ∈ Ioo a b, HasDerivAt y (dy r) r)
    (hbound : ∀ r ∈ Icc a b, dy r ≤ K*y r+e r) :
    ∀ r ∈ Icc a b, y r ≤ (y a+∫ t in a..b, e t)*Real.exp (K*(r-a)) := by
  have hiY := hy.intervalIntegrable_of_Icc (μ := volume) hab
  have hiD := hdy.intervalIntegrable_of_Icc (μ := volume) hab
  have hiE := he.intervalIntegrable_of_Icc (μ := volume) hab
  have hb : ∀ r ∈ Icc a b, y r ≤ (y a+∫ t in a..b, e t)+∫ t in a..r, K*y t := by
    intro r hr
    have hsub : Icc a r ⊆ Icc a b := Icc_subset_Icc le_rfl hr.2
    have hiYr := (hy.mono hsub).intervalIntegrable_of_Icc (μ := volume) hr.1
    have hiEr := (he.mono hsub).intervalIntegrable_of_Icc (μ := volume) hr.1
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 (hy.mono hsub)
      (fun t ht => hD t ⟨ht.1,ht.2.trans_le hr.2⟩)
      ((hdy.mono hsub).intervalIntegrable_of_Icc (μ := volume) hr.1)
    have hcomp := intervalIntegral.integral_mono_on hr.1
      ((hdy.mono hsub).intervalIntegrable_of_Icc (μ := volume) hr.1)
      ((hiYr.const_mul K).add hiEr) (fun t ht => hbound t (hsub ht))
    have hebr : (∫ t in a..r, e t) ≤ ∫ t in a..b, e t := by
      have hepos : 0 ≤ ∫ t in r..b, e t := intervalIntegral.integral_nonneg
        hr.2 (fun t ht => he0 t ⟨hr.1.trans ht.1,ht.2⟩)
      have hesplit := intervalIntegral.integral_add_adjacent_intervals hiEr
        ((he.mono (Icc_subset_Icc hr.1 le_rfl)).intervalIntegrable_of_Icc (μ := volume) hr.2)
      linarith
    rw [hftc,intervalIntegral.integral_add (hiYr.const_mul K) hiEr] at hcomp
    linarith
  have hh := spectral_integral_gronwall a b (y a+∫ t in a..b, e t) hab y (fun _ => K)
    hy continuousOn_const (fun _ _ => hK) hb
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm (b-a) K,
    mul_comm _ K] using hh

end DefocusingNLS

end OAI
