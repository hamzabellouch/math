import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBWeightedPrimitives

namespace OAI

/-! A phase integral controlled by the momentum derivative and endpoint size. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralWKB_phase_integral (a b c B sign : ℝ) (hab : a≤b)
    (hc : 0<c) (hs : sign^2=1) (p g : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hp0 : ∀ t ∈ Icc a b, 0<p t) (hcg : ∀ t ∈ Icc a b, c≤g t)
    (haB : p a≤B) (hbB : p b≤B)
    (hD : ∀ t ∈ Ioo a b, HasDerivAt p (sign*g t/(2*p t)) t) :
    (∫ t in a..b, 1/p t)≤4*B/c := by
  have hi : IntervalIntegrable (fun t => g t/p t) volume a b :=
    (hg.div hp (fun t ht => (hp0 t ht).ne')).intervalIntegrable_of_Icc hab
  have hA : ContinuousOn (fun t => (2*sign)*p t) (Icc a b) := continuousOn_const.mul hp
  have hAD (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun t => (2*sign)*p t) (g t/p t) t := by
    apply ((hD t ht).const_mul (2*sign)).congr_deriv
    calc
      _ = sign^2*(g t/p t) := by ring
      _ = _ := by rw [hs,one_mul]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hA hAD hi
  have hio : IntervalIntegrable (fun t => 1/p t) volume a b :=
    (continuousOn_const.div hp (fun t ht => (hp0 t ht).ne')).intervalIntegrable_of_Icc hab
  have hle : (∫ t in a..b, 1/p t)≤(1/c)*(∫ t in a..b, g t/p t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hio (hi.const_mul _)
    intro t ht
    have hpt := hp0 t ht
    have hh : 1/p t≤g t/(c*p t) := by
      apply (div_le_div_iff₀ hpt (mul_pos hc hpt)).mpr
      simpa only [one_mul,mul_comm c (p t)] using mul_le_mul_of_nonneg_right (hcg t ht) hpt.le
    convert hh using 1
    ring
  have hpa : 0≤p a := (hp0 a ⟨le_rfl,hab⟩).le
  have hpb : 0≤p b := (hp0 b ⟨hab,le_rfl⟩).le
  have hend : (2*sign)*p b-(2*sign)*p a≤4*B := by
    rcases sq_eq_one_iff.mp hs with hs' | hs'
    · rw [hs']; nlinarith
    · rw [hs']; nlinarith
  rw [he] at hle
  calc
    _ ≤ (1/c)*((2*sign)*p b-(2*sign)*p a) := hle
    _ ≤ (1/c)*(4*B) := mul_le_mul_of_nonneg_left hend (by positivity)
    _ = _ := by ring

end DefocusingNLS

end OAI
