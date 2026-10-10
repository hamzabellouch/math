import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralObservationZero
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugePair

namespace OAI

/-! A nonzero weak observation cannot vanish in the exterior physical gauge. -/

open Set
namespace DefocusingNLS

theorem spectralPhysicalGaugePair_values_zero (Q f g : ℝ → ℂ) (r : ℝ)
    (hQ : Q r ≠ 0) (hz : spectralPhysicalGaugePair Q f g r=0) : f r=0 ∧ g r=0 := by
  have hp := congrArg (fun v : (ℂ × ℂ) × (ℂ × ℂ) => v.1.1) hz
  have hm := congrArg (fun v : (ℂ × ℂ) × (ℂ × ℂ) => v.2.1) hz
  change Q r*(f r+Complex.I*g r)=0 at hp
  change star (Q r)*(f r-Complex.I*g r)=0 at hm
  have ha := (mul_eq_zero.mp hp).resolve_left hQ
  have hb := (mul_eq_zero.mp hm).resolve_left (star_ne_zero.mpr hQ)
  have hf : f r=0 := by linear_combination ha/2+hb/2
  have hg : Complex.I*g r=0 := by linear_combination ha/2-hb/2
  exact ⟨hf,(mul_eq_zero.mp hg).resolve_left Complex.I_ne_zero⟩

theorem spectralHarmonicObservation_zero_of_exterior_gauge (ell : ℕ) (L R : ℝ)
    (hL : 0 < L) (hLR : L < R) (u : SpectralHarmonicPair ell R) (Q : ℝ → ℂ)
    (hQ : ∀ r ∈ Ioo L R, Q r ≠ 0)
    (hf : ∀ r ∈ Ioc 0 L,
      spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst r=0)
    (C : ℂ) (hg : ∀ r ∈ Ioc 0 L,
      spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd r=C*(r : ℂ)^ell)
    (he : ∀ r ∈ Ioo L R, spectralPhysicalGaugePair Q
      (spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst)
      (spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd) r=0) :
    spectralHarmonicObservation ell R (hL.trans hLR) u=0 := by
  let f := spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst
  let g := spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd
  have hz (r : ℝ) (hr : r ∈ Ioo L R) : f r=0 ∧ g r=0 :=
    spectralPhysicalGaugePair_values_zero Q f g r (hQ r hr) (he r hr)
  have hfc : ContinuousOn f (Icc L R) :=
    spectralHarmonicRepresentative_continuousOn_closed ell R L (hL.trans hLR) hL u.fst
  have hgc : ContinuousOn g (Icc L R) :=
    spectralHarmonicRepresentative_continuousOn_closed ell R L (hL.trans hLR) hL u.snd
  have hcl : Icc L R ⊆ closure (Ioo L R) := by rw [closure_Ioo hLR.ne]
  have hF : EqOn f 0 (Icc L R) :=
    (show EqOn f 0 (Ioo L R) from fun r hr => (hz r hr).1).of_subset_closure
      hfc continuousOn_const Ioo_subset_Icc_self hcl
  have hG : EqOn g 0 (Icc L R) :=
    (show EqOn g 0 (Ioo L R) from fun r hr => (hz r hr).2).of_subset_closure
      hgc continuousOn_const Ioo_subset_Icc_self hcl
  have hC : C=0 := by
    have hc : C*(L : ℂ)^ell=0 := (hg L ⟨hL,le_rfl⟩).symm.trans (hG ⟨le_rfl,hLR.le⟩)
    exact (mul_eq_zero.mp hc).resolve_right
      (pow_ne_zero ell (Complex.ofReal_ne_zero.mpr hL.ne'))
  apply spectralHarmonicObservation_zero_of_representatives
  · intro r hr
    by_cases hrl : r ≤ L
    · exact hf r ⟨hr.1,hrl⟩
    · exact hF ⟨(lt_of_not_ge hrl).le,hr.2⟩
  · intro r hr
    by_cases hrl : r ≤ L
    · rw [hg r ⟨hr.1,hrl⟩,hC,zero_mul]
    · exact hG ⟨(lt_of_not_ge hrl).le,hr.2⟩

end DefocusingNLS

end OAI
