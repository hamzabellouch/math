import OAI.Geometry.SurfaceImmersion.Atlas.CorrectedSeedCoordinates
import OAI.Geometry.SurfaceImmersion.Correction.NormalizedPolynomialMean

namespace OAI

/-! The polynomial quadratic mean for the actual corrected geometric seeds.
All constants are chosen before the oscillation and amplitude scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes

variable {n : ℕ} {U : Set Base} {O Q : Set LowJet}
variable {F : RField 4} {V : Set SmallModes.Base}

theorem correctedPolynomialMean_bounds
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B₀ F₀ : ℝ) (hB₀ : 1 ≤ B₀) (hF₀ : 0 ≤ F₀)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V) {L : ℕ}
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (q : ℕ) (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N) :
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
      ∀ (b c : SupportedField (F := ℝ) (modeSupport K)) (d : ℝ), 0 ≤ d →
      supportedWeightedSeminorm (modeSupport K) s (m + order P + (q + 1) * (L + 1)) b ≤ A →
      supportedWeightedSeminorm (modeSupport K) s (m + order P + (q + 1) * (L + 1)) c ≤ A →
      supportedWeightedSeminorm (modeSupport K) s (m + order P + (q + 1) * (L + 1)) (b - c) ≤ A * d →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
      let Zb := coordinateCorrectedSeed δ τ hF h K hKV R q b
      let Zc := coordinateCorrectedSeed δ τ hF h K hKV R q c
      WeightedBound U s m ((τ / s + ε / τ ^ p) * E)
        (normalizedPolynomialMean P δ ε G φ Zb τ t) ∧
      WeightedBound U s m ((τ / s + ε / τ ^ p) * (2 * E) * d)
        (fun x => normalizedPolynomialMean P δ ε G φ Zb τ t x -
          normalizedPolynomialMean P δ ε G φ Zc τ t x) := by
  obtain ⟨E₀, hE₀, he⟩ := normalizedPolynomialMean_bounds hU hO hQ hQO P hP m B₀ F₀ hB₀ hF₀
  let S := correctedSeedBudget L B D q (m + order P) N
  have hS : 0 ≤ S := correctedSeedBudget_nonneg L B D hB q (m + order P) hN
  refine ⟨E₀ * (S * A) ^ 2, mul_nonneg hE₀ (sq_nonneg _), ?_⟩
  intro G φ hG hφ s δ τ ε p hδ hτ hs hτs hs1 hε hε1 hp hsmall hGQ hGb hφb hc R hR hbN b c d hd hb hcb hbc t ht
  let Zb := coordinateCorrectedSeed δ τ hF h K hKV R q b
  let Zc := coordinateCorrectedSeed δ τ hF h K hKV R q c
  have hzb : supportedWeightedSeminorm K s (m + order P) Zb ≤ S * A * (δ * τ) :=
    coordinateCorrectedSeed_bound δ τ hF h K hKV hδ.le hτ hs hτs hs1 hε hsmall
      B D hB hD hc R hR q (m + order P) A N hA hN hbN b hb
  have hzc : supportedWeightedSeminorm K s (m + order P) Zc ≤ S * A * (δ * τ) :=
    coordinateCorrectedSeed_bound δ τ hF h K hKV hδ.le hτ hs hτs hs1 hε hsmall
      B D hB hD hc R hR q (m + order P) A N hA hN hbN c hcb
  have hzd : supportedWeightedSeminorm K s (m + order P) (Zb - Zc) ≤ S * (A * d) * (δ * τ) := by
    have hh := coordinateCorrectedSeed_bound δ τ hF h K hKV hδ.le hτ hs hτs hs1 hε hsmall
      B D hB hD hc R hR q (m + order P) (A * d) N (mul_nonneg hA hd) hN hbN (b - c) hbc
    rw [coordinateCorrectedSeed_sub] at hh
    exact hh
  have hh := he G φ hG hφ K Zb Zc s δ τ ε (S * A) (S * (A * d)) p
    hδ hτ hs hτs hs1 hε hε1 (mul_nonneg hS hA) (mul_nonneg hS (mul_nonneg hA hd))
    hp hGQ hGb hφb hzb hzc hzd t ht
  dsimp only
  constructor
  · convert hh.1 using 1
    ring
  · convert hh.2 using 1
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
