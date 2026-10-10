import OAI.Geometry.EinsteinFour.GeodesicAverage

namespace OAI

/-! Invariance of the geodesic-flow measure supplies the stationarity needed
by the mean-square averaging estimate. This is a direct change of variables
in the actual field integrals. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- It suffices to bound the derivative energy at time zero: preservation of
the field measure transports both energy identities to every time. -/
theorem invariant_geodesic_mean_square_lower
    (φ : ℝ → Ω ≃ᵐ Ω) (hφ : ∀ r, MeasurePreserving (φ r) μ μ)
    (C H : C(Ω, E)) {F G : ℝ → C(Ω, E)} {t : ℝ}
    (hfield : ∀ r x, F r x = C (φ r x))
    (hgradient : ∀ r x, G r x = H (φ r x))
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (henergy : (∫ x, ‖H x‖ ^ 2 ∂μ) ≤ (3 / 2) * (∫ x, ‖C x‖ ^ 2 ∂μ)) :
    (∫ x, ‖C x‖ ^ 2 ∂μ) * (1 - (t / Real.pi) ^ 2 / 2) ≤
      ∫ x, ‖∫ u, F (t * u) x ∂sineMeasure‖ ^ 2 ∂μ := by
  apply geodesic_mean_square_lower (integral_nonneg fun _ => sq_nonneg _) hderiv
  · intro r
    simpa only [hfield] using (hφ r).integral_comp' (fun x => ‖C x‖ ^ 2)
  · intro r
    have he := (hφ r).integral_comp' (fun x => ‖H x‖ ^ 2)
    simpa only [hgradient, he] using henergy

end

end PositiveEinsteinFour.Averages

end OAI
