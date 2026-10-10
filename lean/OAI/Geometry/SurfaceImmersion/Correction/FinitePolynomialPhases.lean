import OAI.Geometry.SurfaceImmersion.Geometry.FiniteQuadraticVariation

namespace OAI

/-! Exact finite expansion of the polynomial quadratic term before
separating its zero phases. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma half_second_variation_sum {ι : Type*} [Fintype ι]
    (e : Expression) (G : Base → Space) (H : ι → Base → Fin 4 → ℂ)
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval
      ![G, realField (fun p => ∑ i, H i p), realField (fun p => ∑ i, H i p), 0] z =
      (∑ i, ∑ j, (quadraticComplex e G (complexJet (H i)) (complexJet (H j)) z).re / 4) +
      ∑ i, ∑ j, (quadraticComplex e G (complexJet (H i))
        (starDirectionJets (complexJet (H j))) z).re / 4 := by
  have hsum : ContDiff ℝ ∞ (fun p => ∑ i, H i p) := ContDiff.sum (fun i _ => hH i)
  rw [half_second_variation_real e G hsum, complexJet_sum Finset.univ H (fun i _ => hH i),
    starDirectionJets_sum, quadraticComplex_sum, quadraticComplex_sum]
  simp only [Complex.re_sum, Finset.sum_div, add_div]


def oscillatorySum {ι : Type*} [Fintype ι] (τ : ℝ) (φ : ι → Base → ℝ)
    (H : ι → Base → Fin 4 → ℂ) : Base → Fin 4 → ℂ :=
  fun p => ∑ i, phase τ (φ i) p • H i p

theorem half_second_variation_phases {ι : Type*} [Fintype ι]
    (e : Expression) (G : Base → Space) (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i)) (τ : ℝ) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval
      ![G, realField (oscillatorySum τ φ H), realField (oscillatorySum τ φ H), 0] z =
      (∑ i, ∑ j, ((phase τ (φ i) z.1 * phase τ (φ j) z.1) *
        conjugatedVariation e G (pairPhases (φ i) (φ j)) (pairDirections (H i) (H j)) τ 1 z).re / 4) +
      ∑ i, ∑ j, ((phase τ (φ i) z.1 * phase τ (fun p => -φ j p) z.1) *
        conjugatedVariation e G (pairPhases (φ i) (fun p => -φ j p))
          (pairDirections (H i) (starField (H j))) τ 1 z).re / 4 := by
  have hsm (i : ι) : ContDiff ℝ ∞ (fun p => phase τ (φ i) p • H i p) :=
    (phase_smooth (hφ i) τ).smul (hH i)
  rw [show oscillatorySum τ φ H = fun p => ∑ i, phase τ (φ i) p • H i p from rfl,
    half_second_variation_sum e G _ hsm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [quadraticComplex_phase_factor]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← complexJet_starField (hsm j), starField_phase, quadraticComplex_phase_factor]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
