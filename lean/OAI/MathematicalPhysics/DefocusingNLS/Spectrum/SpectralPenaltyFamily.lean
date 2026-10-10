import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyWeakEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicPenaltyLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedCoreWeak

namespace OAI

/-! Coefficient hypotheses for the singular pressure limit. All fields concern
the scalar coefficients; the inverse and its convergence are conclusions. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

structure SpectralPenaltyFamily (R l : ℝ) where
  weight : ℕ → SpectralHarmonicWeight R
  limitWeight : SpectralHarmonicWeight R
  lower : ℝ
  lower_pos : 0 < lower
  radial_lower : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, lower ≤ (weight n).density r
  angular_lower : ∀ n, ∀ᵐ r ∂spectralAngularMeasure R, lower ≤ (weight n).density r
  limit_radial_lower : ∀ᵐ r ∂radialPressureMeasure R, lower ≤ limitWeight.density r
  limit_angular_lower : ∀ᵐ r ∂spectralAngularMeasure R, lower ≤ limitWeight.density r
  error : ℕ → ℝ
  error_nonneg : ∀ n, 0 ≤ error n
  error_zero : Tendsto error atTop (𝓝 0)
  radial_error : ∀ n, ∀ᵐ r ∂radialPressureMeasure R,
    ‖(weight n).density r-limitWeight.density r‖ ≤ error n
  angular_error : ∀ n, ∀ᵐ r ∂spectralAngularMeasure R,
    ‖(weight n).density r-limitWeight.density r‖ ≤ error n
  pressure : ℕ → ℝ → ℝ
  pressure_measurable : ∀ n, AEStronglyMeasurable (pressure n) (radialPressureMeasure R)
  pressure_bound : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖pressure n r‖ ≤ 1
  pressure_nonneg : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ pressure n r
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_zero : Tendsto scale atTop (𝓝 0)
  corePressure : ℝ
  corePressure_pos : 0 < corePressure
  pressure_weak : ∀ f : ℝ → ℝ, Integrable f (radialPressureMeasure R) →
    Tendsto (fun n => ∫ r, pressure n r*f r ∂radialPressureMeasure R) atTop
      (𝓝 (∫ r, (Iic l).indicator (fun _ : ℝ => corePressure) r*f r ∂radialPressureMeasure R))
  pressure_away : ∀ d : ℝ, 0 < d → ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧
    Tendsto η atTop (𝓝 0) ∧ ∀ n, ∀ᵐ r ∂radialPressureMeasure R,
      l+d < r → ‖(scale n)⁻¹*((weight n).density r*pressure n r)‖ ≤ η n

namespace SpectralPenaltyFamily
variable {R l : ℝ}

noncomputable def inverse (s : SpectralPenaltyFamily R l) (ell n : ℕ) :
    StrongDual ℝ (SpectralHarmonicPair ell R) →L[ℝ] SpectralHarmonicPair ell R :=
  spectralHarmonicPenaltyInverse ell R (s.weight n) s.lower s.lower_pos
    (s.radial_lower n) (s.angular_lower n) (s.pressure n) (s.pressure_measurable n)
    (s.pressure_bound n) (s.pressure_nonneg n) (s.scale n) (s.scale_pos n)

noncomputable def limitInverse (s : SpectralPenaltyFamily R l) (ell : ℕ) :
    StrongDual ℝ (SpectralHarmonicPair ell R) →L[ℝ] SpectralHarmonicPair ell R :=
  spectralHarmonicCoreInverse ell R l s.limitWeight s.lower s.lower_pos
    s.limit_radial_lower s.limit_angular_lower

theorem inverse_norm (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) : ‖s.inverse ell n F‖ ≤ ‖F‖/s.lower :=
  spectralHarmonicPenaltyInverse_norm ell R (s.weight n) s.lower s.lower_pos
    (s.radial_lower n) (s.angular_lower n) (s.pressure n) (s.pressure_measurable n)
    (s.pressure_bound n) (s.pressure_nonneg n) (s.scale n) (s.scale_pos n) F

def reindex (s : SpectralPenaltyFamily R l) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    SpectralPenaltyFamily R l where
  weight := s.weight ∘ φ
  limitWeight := s.limitWeight
  lower := s.lower
  lower_pos := s.lower_pos
  radial_lower n := s.radial_lower (φ n)
  angular_lower n := s.angular_lower (φ n)
  limit_radial_lower := s.limit_radial_lower
  limit_angular_lower := s.limit_angular_lower
  error := s.error ∘ φ
  error_nonneg n := s.error_nonneg (φ n)
  error_zero := s.error_zero.comp hφ
  radial_error n := s.radial_error (φ n)
  angular_error n := s.angular_error (φ n)
  pressure := s.pressure ∘ φ
  pressure_measurable n := s.pressure_measurable (φ n)
  pressure_bound n := s.pressure_bound (φ n)
  pressure_nonneg n := s.pressure_nonneg (φ n)
  scale := s.scale ∘ φ
  scale_pos n := s.scale_pos (φ n)
  scale_zero := s.scale_zero.comp hφ
  corePressure := s.corePressure
  corePressure_pos := s.corePressure_pos
  pressure_weak f hf := (s.pressure_weak f hf).comp hφ
  pressure_away d hd := by
    obtain ⟨η,hη,hη0,hηb⟩ := s.pressure_away d hd
    exact ⟨η ∘ φ,fun n => hη (φ n),hη0.comp hφ,fun n => hηb (φ n)⟩

theorem weak_limit_unique (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (F : ℕ → StrongDual ℝ (SpectralHarmonicPair ell R))
    (F₀ : StrongDual ℝ (SpectralHarmonicPair ell R)) (M : ℝ) (hF : ∀ n, ‖F n‖ ≤ M)
    (hF0 : ∀ v, Tendsto (fun n => F n v) atTop (𝓝 (F₀ v)))
    (u₀ : SpectralHarmonicPair ell R)
    (hu : ∀ L : SpectralHarmonicPair ell R →L[ℝ] ℝ,
      Tendsto (fun n => L (s.inverse ell n (F n))) atTop (𝓝 (L u₀))) :
    u₀=s.limitInverse ell F₀ := by
  have hb (n : ℕ) : ‖s.inverse ell n (F n)‖ ≤ M/s.lower :=
    (s.inverse_norm ell n (F n)).trans (div_le_div_of_nonneg_right (hF n) s.lower_pos.le)
  have hv := spectralHarmonicFirstValue_weakSequence ell R (hl.trans hlR)
    (fun n => s.inverse ell n (F n)) u₀ (M/s.lower) hb hu
  have hc := spectralHarmonicPenaltyInverse_core_limit ell R l s.corePressure s.corePressure_pos
    s.weight s.lower s.lower_pos s.radial_lower s.angular_lower s.pressure
    s.pressure_measurable s.pressure_bound s.pressure_nonneg s.scale s.scale_pos s.scale_zero
    F M hF s.pressure_weak u₀ hv
  have he := spectralHarmonicPenalty_weak_equation ell R l hl hlR s.weight s.limitWeight
    s.error s.error_nonneg s.error_zero s.radial_error s.angular_error s.pressure
    s.pressure_measurable s.pressure_bound s.scale s.pressure_away F F₀ hF0
    (fun n => s.inverse ell n (F n)) u₀ (M/s.lower) hb hu
    (fun n v => spectralHarmonicPenaltyInverse_equation ell R (s.weight n) s.lower s.lower_pos
      (s.radial_lower n) (s.angular_lower n) (s.pressure n) (s.pressure_measurable n)
      (s.pressure_bound n) (s.pressure_nonneg n) (s.scale n) (s.scale_pos n) (F n) v)
  exact spectralHarmonicCoreInverse_unique ell R l s.limitWeight s.lower s.lower_pos
    s.limit_radial_lower s.limit_angular_lower F₀ u₀ hc (fun v => he v v.property)

end SpectralPenaltyFamily
end DefocusingNLS

end OAI
