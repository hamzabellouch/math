import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactPencil

namespace OAI

/-! The compact-pencil kernels are exactly the penalized and constrained weak
equations, with no regularity or eigenfunction identification assumed. -/

open InnerProductSpace
namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

noncomputable def penaltyForm (s : SpectralPenaltyFamily R l) (ell n : ℕ) :
    SpectralHarmonicPair ell R →L[ℝ] SpectralHarmonicPair ell R →L[ℝ] ℝ :=
  spectralCoercivePenaltyForm (spectralHarmonicPairForm ell R (s.weight n))
    (spectralHarmonicFirstValue ell R)
    (spectralWeightedPressure R (s.weight n) (s.pressure n)
      (s.pressure_measurable n) (s.pressure_bound n)) (s.scale n)

theorem penaltyForm_coercive (s : SpectralPenaltyFamily R l) (ell n : ℕ) :
    IsCoercive (s.penaltyForm ell n) := by
  apply spectralCoercivePenaltyForm_coercive _ s.lower s.lower_pos
    (spectralHarmonicPairForm_lower ell R (s.weight n) s.lower
      (s.radial_lower n) (s.angular_lower n))
  · exact spectralWeightedPressure_nonneg R (s.weight n)
      ((s.radial_lower n).mono (fun _ h => s.lower_pos.le.trans h)) (s.pressure n)
      (s.pressure_measurable n) (s.pressure_bound n) (s.pressure_nonneg n)
  · exact s.scale_pos n

theorem inverse_equation (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) (v : SpectralHarmonicPair ell R) :
    s.penaltyForm ell n (s.inverse ell n F) v=F v :=
  spectralCoerciveInverse_equation (s.penaltyForm ell n) (s.penaltyForm_coercive ell n) F v

theorem inverse_unique (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) (u : SpectralHarmonicPair ell R)
    (hu : ∀ v, s.penaltyForm ell n u v=F v) : u=s.inverse ell n F :=
  spectralCoerciveInverse_unique (s.penaltyForm ell n) (s.penaltyForm_coercive ell n) F u hu

theorem compactPencil_variational (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (hR : 0 < R) (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (z : SpectralRadialObservationSpace R) :
    s.compactPencil ell hR n K z=z ↔
      ∃ u : SpectralHarmonicPair ell R, spectralHarmonicObservation ell R hR u=z ∧
        ∀ v, s.penaltyForm ell n u v=inner ℝ (K z) v := by
  let F := toDual ℝ (SpectralHarmonicPair ell R) (K z)
  have hobs : s.compactPencil ell hR n K z=
      spectralHarmonicObservation ell R hR (s.inverse ell n F) := rfl
  constructor
  · intro h
    refine ⟨s.inverse ell n F,hobs.symm.trans h,?_⟩
    exact fun v => s.inverse_equation ell n F v
  · rintro ⟨u,hu,hv⟩
    have he := s.inverse_unique ell n F u hv
    rw [hobs,← he]
    exact hu

theorem limitPencil_variational (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (z : SpectralRadialObservationSpace R) :
    s.limitPencil ell hl hlR K z=z ↔
      ∃ u : SpectralHarmonicPair ell R, u ∈ spectralHarmonicCoreSubspace ell R l ∧
        spectralHarmonicObservation ell R (hl.trans hlR) u=z ∧
        ∀ v : SpectralHarmonicCore ell R l,
          spectralHarmonicPairForm ell R s.limitWeight u v=inner ℝ (K z) v := by
  let F := toDual ℝ (SpectralHarmonicPair ell R) (K z)
  have hobs : s.limitPencil ell hl hlR K z=
      spectralHarmonicObservation ell R (hl.trans hlR) (s.limitInverse ell F) := rfl
  constructor
  · intro h
    refine ⟨s.limitInverse ell F,?_,hobs.symm.trans h,?_⟩
    · exact spectralHarmonicCoreInverse_mem ell R l s.limitWeight s.lower s.lower_pos
        s.limit_radial_lower s.limit_angular_lower F
    · exact fun v => spectralHarmonicCoreInverse_equation ell R l s.limitWeight
        s.lower s.lower_pos s.limit_radial_lower s.limit_angular_lower F v
  · rintro ⟨u,hcore,hu,hv⟩
    have he : u=s.limitInverse ell F :=
      spectralHarmonicCoreInverse_unique ell R l s.limitWeight s.lower s.lower_pos
        s.limit_radial_lower s.limit_angular_lower F u hcore hv
    rw [hobs,← he]
    exact hu

end DefocusingNLS.SpectralPenaltyFamily

end OAI
