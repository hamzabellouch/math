import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeObservation

namespace OAI

/-! Exterior physical values and regular core continuation determine the
entire compact observation, including its boundary traces. -/

open Set
namespace DefocusingNLS

theorem spectralHarmonicRepresentative_sub_smul (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u v : SpectralHarmonicEnergy ell R) (a : ℂ) (r : ℝ) :
    spectralHarmonicRepresentative ell R hR (u - a • v) r =
      spectralHarmonicRepresentative ell R hR u r -
        a * spectralHarmonicRepresentative ell R hR v r := by
  unfold spectralHarmonicRepresentative spectralRadialRepresentative
  split_ifs <;> simp only [map_sub, map_smul, smul_eq_mul, mul_zero, sub_self]

theorem spectralHarmonicObservation_zero_of_core_exterior (ell : ℕ) (L R : ℝ)
    (hL : 0 < L) (hLR : L < R) (u : SpectralHarmonicPair ell R)
    (hf : ∀ r ∈ Ioc 0 L,
      spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst r = 0)
    (C : ℂ) (hg : ∀ r ∈ Ioc 0 L,
      spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd r = C * (r : ℂ)^ell)
    (he : ∀ r ∈ Ioo L R,
      spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst r = 0 ∧
      spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd r = 0) :
    spectralHarmonicObservation ell R (hL.trans hLR) u = 0 := by
  let f := spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst
  let g := spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd
  have hcl : Icc L R ⊆ closure (Ioo L R) := by rw [closure_Ioo hLR.ne]
  have hF : EqOn f 0 (Icc L R) :=
    (show EqOn f 0 (Ioo L R) from fun r hr => (he r hr).1).of_subset_closure
      (spectralHarmonicRepresentative_continuousOn_closed ell R L (hL.trans hLR) hL u.fst)
      continuousOn_const Ioo_subset_Icc_self hcl
  have hG : EqOn g 0 (Icc L R) :=
    (show EqOn g 0 (Ioo L R) from fun r hr => (he r hr).2).of_subset_closure
      (spectralHarmonicRepresentative_continuousOn_closed ell R L (hL.trans hLR) hL u.snd)
      continuousOn_const Ioo_subset_Icc_self hcl
  have hC : C = 0 := by
    have hh : C * (L : ℂ)^ell = 0 := (hg L ⟨hL, le_rfl⟩).symm.trans (hG ⟨le_rfl, hLR.le⟩)
    exact (mul_eq_zero.mp hh).resolve_right
      (pow_ne_zero ell (Complex.ofReal_ne_zero.mpr hL.ne'))
  apply spectralHarmonicObservation_zero_of_representatives
  · intro r hr
    by_cases hrl : r ≤ L
    · exact hf r ⟨hr.1, hrl⟩
    · exact hF ⟨(lt_of_not_ge hrl).le, hr.2⟩
  · intro r hr
    by_cases hrl : r ≤ L
    · rw [hg r ⟨hr.1, hrl⟩, hC, zero_mul]
    · exact hG ⟨(lt_of_not_ge hrl).le, hr.2⟩

theorem spectralHarmonicObservation_eq_of_gauge_values (ell : ℕ) (L R : ℝ)
    (hL : 0 < L) (hLR : L < R) (u v : SpectralHarmonicPair ell R)
    (Q : ℝ → ℂ) (hQ : ∀ r ∈ Ioo L R, Q r ≠ 0) (a C D : ℂ)
    (hfu : ∀ r ∈ Ioc 0 L, spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst r = 0)
    (hfv : ∀ r ∈ Ioc 0 L, spectralHarmonicRepresentative ell R (hL.trans hLR) v.fst r = 0)
    (hgu : ∀ r ∈ Ioc 0 L, spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd r = C*(r : ℂ)^ell)
    (hgv : ∀ r ∈ Ioc 0 L, spectralHarmonicRepresentative ell R (hL.trans hLR) v.snd r = D*(r : ℂ)^ell)
    (he : ∀ r ∈ Ioo L R,
      (spectralPhysicalGaugePair Q
        (spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst)
        (spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd) r).1.1 =
        a * (spectralPhysicalGaugePair Q
          (spectralHarmonicRepresentative ell R (hL.trans hLR) v.fst)
          (spectralHarmonicRepresentative ell R (hL.trans hLR) v.snd) r).1.1 ∧
      (spectralPhysicalGaugePair Q
        (spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst)
        (spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd) r).2.1 =
        a * (spectralPhysicalGaugePair Q
          (spectralHarmonicRepresentative ell R (hL.trans hLR) v.fst)
          (spectralHarmonicRepresentative ell R (hL.trans hLR) v.snd) r).2.1) :
    spectralHarmonicObservation ell R (hL.trans hLR) u =
      a • spectralHarmonicObservation ell R (hL.trans hLR) v := by
  have hz : spectralHarmonicObservation ell R (hL.trans hLR) (u - a • v) = 0 := by
    refine spectralHarmonicObservation_zero_of_core_exterior ell L R hL hLR (u - a • v)
      ?_ (C - a * D) ?_ ?_
    · intro r hr
      change spectralHarmonicRepresentative ell R (hL.trans hLR) (u.fst - a • v.fst) r = 0
      rw [spectralHarmonicRepresentative_sub_smul, hfu r hr, hfv r hr]
      ring
    · intro r hr
      change spectralHarmonicRepresentative ell R (hL.trans hLR) (u.snd - a • v.snd) r = _
      rw [spectralHarmonicRepresentative_sub_smul, hgu r hr, hgv r hr]
      ring
    · intro r hr
      have hp := (he r hr).1
      have hm := (he r hr).2
      dsimp only [spectralPhysicalGaugePair] at hp hm
      have hplus :
          spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst r +
            Complex.I * spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd r =
          a * (spectralHarmonicRepresentative ell R (hL.trans hLR) v.fst r +
            Complex.I * spectralHarmonicRepresentative ell R (hL.trans hLR) v.snd r) := by
        apply mul_left_cancel₀ (hQ r hr)
        calc
          _ = a * (Q r * _) := hp
          _ = _ := by ring
      have hminus :
          spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst r -
            Complex.I * spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd r =
          a * (spectralHarmonicRepresentative ell R (hL.trans hLR) v.fst r -
            Complex.I * spectralHarmonicRepresentative ell R (hL.trans hLR) v.snd r) := by
        apply mul_left_cancel₀ (star_ne_zero.mpr (hQ r hr))
        calc
          _ = a * (star (Q r) * _) := hm
          _ = _ := by ring
      constructor
      · change spectralHarmonicRepresentative ell R (hL.trans hLR) (u.fst - a • v.fst) r = 0
        rw [spectralHarmonicRepresentative_sub_smul]
        linear_combination (hplus + hminus) / 2
      · change spectralHarmonicRepresentative ell R (hL.trans hLR) (u.snd - a • v.snd) r = 0
        rw [spectralHarmonicRepresentative_sub_smul]
        apply (mul_eq_zero.mp (show Complex.I *
          (spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd r -
            a * spectralHarmonicRepresentative ell R (hL.trans hLR) v.snd r) = 0 from ?_)).resolve_left Complex.I_ne_zero
        linear_combination (hplus - hminus) / 2
  rw [map_sub, map_smul, sub_eq_zero] at hz
  exact hz

end DefocusingNLS

end OAI
