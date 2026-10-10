import OAI.Geometry.SurfaceImmersion.Correction.CorrectedPolynomialMean
import OAI.Geometry.SurfaceImmersion.Correction.NormalizedPolynomialMean
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedRootAmplitude

namespace OAI

/-! The polynomial mean on actual cutoff square-root trial amplitudes.
Its constants are uniform before choosing the oscillation scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes

variable {n : ℕ} {U : Set Base} {O Q : Set LowJet}
variable {F : RField 4} {V : Set SmallModes.Base}

theorem correctedPolynomialRootMean_bounds
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B₀ F₀ : ℝ) (hB₀ : 1 ≤ B₀) (hF₀ : 0 ≤ F₀)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V) {L : ℕ}
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (q : ℕ) {r R₀ C P₀ N : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (hP₀ : 0 ≤ P₀) (hN : 0 ≤ N) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (_hG : ContDiff ℝ ∞ G) (_hφ : ContDiff ℝ ∞ φ)
      (s : ℝ≥0) (δ τ ε : ℝ) (p : ℕ),
      0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      loss P ≤ p → τ / s + ε / τ ^ p ≤ 1 →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B₀ (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) F₀ (fun x => fderiv ℝ φ x (coordinateVector v))) →
      (∀ m, SmallModes.ReconstructionCoefficientBound (fun x => complexify (F x)) V s (m + 1) (B m)) →
      ∀ (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
        SupportedField (F := Fin 3 → ℂ) (modeSupport K)),
      (∀ m Z, supportedWeightedSeminorm (modeSupport K) s m (R Z) ≤
        ε / τ ^ p * D m * supportedWeightedSeminorm (modeSupport K) s (m + L) Z) →
      WeightedBound V s (m + order P + (q + 1) * (L + 1)) N (freeNormal F) →
      ∀ (ψ : SupportedField (F := ℝ) (modeSupport K))
        (u v : SmallModes.Base → ℝ) (hu : ContDiffOn ℝ ∞ u V) (hv : ContDiffOn ℝ ∞ v V)
        (hru : Set.MapsTo u V (Set.Icc r R₀)) (hrv : Set.MapsTo v V (Set.Icc r R₀))
        (d : ℝ), 0 ≤ d →
      supportedWeightedSeminorm (modeSupport K) s (m + order P + (q + 1) * (L + 1)) ψ ≤ P₀ →
      WeightedBound V s (m + order P + (q + 1) * (L + 1)) C u →
      WeightedBound V s (m + order P + (q + 1) * (L + 1)) C v →
      WeightedBound V s (m + order P + (q + 1) * (L + 1)) d (fun x => u x - v x) →
      let b := supportedRootAmplitude h.isOpen (modeSupport K) hKV ψ u hu (fun _ hx => hr.trans_le (hru hx).1)
      let c := supportedRootAmplitude h.isOpen (modeSupport K) hKV ψ v hv (fun _ hx => hr.trans_le (hrv hx).1)
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
      let Zb := coordinateCorrectedSeed δ τ hF h K hKV R q b
      let Zc := coordinateCorrectedSeed δ τ hF h K hKV R q c
      WeightedBound U s m ((τ / s + ε / τ ^ p) * E)
        (normalizedPolynomialMean P δ ε G φ Zb τ t) ∧
      WeightedBound U s m ((τ / s + ε / τ ^ p) * (2 * E) * d)
        (fun x => normalizedPolynomialMean P δ ε G φ Zb τ t x -
          normalizedPolynomialMean P δ ε G φ Zc τ t x) := by
  obtain ⟨A, hA, ha⟩ := supportedRootAmplitude_bounds h.isOpen (modeSupport K) hKV
    (R := R₀) hr hC hP₀ (m + order P + (q + 1) * (L + 1))
  obtain ⟨E, hE, he⟩ := correctedPolynomialMean_bounds hU hO hQ hQO P hP m B₀ F₀ hB₀ hF₀
    hF h K hKV B D hB hD q A N (zero_le_one.trans hA) hN
  refine ⟨E, hE, ?_⟩
  intro G φ hG hφ s δ τ ε p hδ hτ hs hτs hs1 hε hε1 hp hsmall hGQ hGb hφb hc R hR hbN ψ u v hu hv hru hrv d hd hψ hbu hbv hdu
  obtain ⟨hbu', hbv', hdu'⟩ := ha s ψ u v hu hv hru hrv d hs hd hψ hbu hbv hdu
  dsimp only
  exact he G φ hG hφ s δ τ ε p hδ hτ hs hτs hs1 hε hε1 hp hsmall hGQ hGb hφb hc R hR hbN
    _ _ d hd hbu' hbv' hdu'

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
