import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingForcing

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling CouplingMarginalBounds
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_top_conditional_probability (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      p.coordinate i (point p hr false ω) < u → u ≤ 1 - width (p.a s) (p.b s) which →
      rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) / 10 ≤
        ((law p j)⟦label i ⁻¹' {topLabel which} |
          MeasurableSpace.comap (point p hr false) inferInstance⟧) ω := by
  let := posterior_isMarkov hp j false i
  have hρ0 : 0 ≤ rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) :=
    rho_nonneg (CircleParameterLaws.coupling_kappa_bounds s hs).1
  filter_upwards [ae_top_posterior_lower hp j hr hs hi which,
    condExp_single_label_point hp j hr false i (topLabel which)] with ω hlo heq
  intro u hxu hu
  rw [heq]
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hlo u hxu hu)
  simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_ofReal hρ0,
    ENNReal.toReal_ofNat] using h

lemma ae_bottom_conditional_probability (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ,
      u ≤ p.coordinate i (point p hr true ω) → width (p.a s) (p.b s) which ≤ u →
      rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) / 10 ≤
        ((law p j)⟦label i ⁻¹' {bottomLabel which} |
          MeasurableSpace.comap (point p hr true) inferInstance⟧) ω := by
  let := posterior_isMarkov hp j true i
  have hρ0 : 0 ≤ rho (kappa s) (p.m s) (width (p.a s) (p.b s) which) :=
    rho_nonneg (CircleParameterLaws.coupling_kappa_bounds s hs).1
  filter_upwards [ae_bottom_posterior_lower hp j hr hs hi which,
    condExp_single_label_point hp j hr true i (bottomLabel which)] with ω hlo heq
  intro u huy hu
  rw [heq]
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hlo u huy hu)
  simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_ofReal hρ0,
    ENNReal.toReal_ofNat] using h

end Invariant233.CircleCoupling

end

end OAI
