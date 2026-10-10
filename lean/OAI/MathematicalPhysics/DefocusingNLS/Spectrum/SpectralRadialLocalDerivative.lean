import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialDerivativeUpgrade

namespace OAI

/-! A locally continuous weak derivative is the classical derivative of the radial representative. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralRadialRepresentative_hasDerivAt_local (R a b : ℝ) (hR : 0 < R)
    (ha : 0 < a) (hbR : b ≤ R) (u : SpectralRadialEnergy R)
    (F : ℝ → ℂ) (hF : ContinuousOn F (Ioo a b))
    (hD : ∀ᵐ t, t ∈ Ioo a b → spectralRadialDerivative R u t=F t)
    (x : ℝ) (hx : x ∈ Ioo a b) :
    HasDerivAt (spectralRadialRepresentative R hR u) (F x) x := by
  let a' := (a+x)/2
  let b' := (x+b)/2
  have hax : a < a' ∧ a' < x := by dsimp only [a']; constructor <;> linarith [hx.1]
  have hxb : x < b' ∧ b' < b := by dsimp only [b']; constructor <;> linarith [hx.2]
  have hab' : a' ≤ b' := le_of_lt (hax.2.trans hxb.1)
  let clamp := fun t : ℝ => max a' (min b' t)
  have hc (t : ℝ) : clamp t ∈ Icc a' b' :=
    ⟨le_max_left _ _,max_le hab' (min_le_left _ _)⟩
  have hs : Icc a' b' ⊆ Ioo a b := fun t ht => ⟨hax.1.trans_le ht.1,ht.2.trans_lt hxb.2⟩
  have hfix (t : ℝ) (ht : t ∈ Icc a' b') : clamp t=t := by
    dsimp only [clamp]
    rw [min_eq_right ht.2,max_eq_right ht.1]
  have hd := spectralRadialRepresentative_hasDerivAt R a' b' hR (ha.trans hax.1)
    (hxb.2.le.trans hbR) u (fun t => F (clamp t))
    (hF.comp_continuous (by fun_prop) (fun t => hs (hc t))) (by
      filter_upwards [hD] with t ht htab
      simpa only [hfix t htab] using ht (hs htab)) x ⟨hax.2,hxb.1⟩
  simpa only [hfix x ⟨hax.2.le,hxb.1.le⟩] using hd

end DefocusingNLS

end OAI
