import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCorrectionEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialCorrection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingJetLimit

namespace OAI

/-! The inverse-defined corrections are actual outgoing ODE solutions; their
norm convergence gives convergence of the complete columns. -/

open Filter Topology Set Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularInverseCorrection (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (r : CircularTailSpace) :
    CircularTailSpace :=
  Ring.inverse (1-circularTailCLM κ hκ*circularFieldOperator νp νm η m hm q)
    (circularTailCLM κ hκ r)

theorem circularInversePolynomial_hasDerivAt (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ)
    (P : ℂ[X]) (U : ℂ[X] × ℂ[X]) (r : CircularTailSpace)
    (hu : IsUnit (1-circularTailCLM κ hκ*circularFieldOperator νp νm η m hm q))
    (t : ℝ)
    (hr : Real.exp (-κ*t) • circularTailEvaluation r t=
      (circularBoundedField νp νm η m (q t) (circularPolynomialJet U t)-
       circularBoundedField νp νm η m (radialExteriorPolynomialFunction P t)
         (circularPolynomialJet U t))-circularPolynomialResidualJet νp νm η m P U t) :
    let v := circularInverseCorrection κ hκ νp νm η m hm q r
    HasDerivAt (fun s => circularPolynomialJet U s+circularUnweight κ v s)
      (circularLeadingField t (circularPolynomialJet U t+circularUnweight κ v t)+
        circularBoundedField νp νm η m (q t)
          (circularPolynomialJet U t+circularUnweight κ v t)) t := by
  intro v
  apply circularPolynomial_corrected νp νm η m P U (circularUnweight κ v) (q t) t
  have hd := circularInverseCorrection_hasDerivAt κ hκ νp νm η m hm q r hu t
  have hw := circularUnweight_hasDerivAt κ t νp νm η m (q t) v
    (circularTailEvaluation r t) hd
  simpa only [hr,add_sub_assoc] using hw

theorem circularInverseCorrection_free_tendsto (κ : ℝ) (hκ : 0 < κ)
    (νp νm : ℕ → ℂ) (μp μm η : ℂ)
    (hp : Tendsto νp atTop (𝓝 μp)) (hn : Tendsto νm atTop (𝓝 μm))
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n) (q : ℕ → ℝ →ᵇ ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hq : ∀ᶠ n in atTop, ∀ t,
      ‖spectralDiagonalCoefficient (m n) (q n t)‖+‖spectralCrossCoefficient (m n) (q n t)‖ ≤ δ n)
    (hgap : circularFieldBound μp μm η 1 ‖(0 : ℝ →ᵇ ℂ)‖ < κ)
    (r : ℕ → CircularTailSpace) (r₀ : CircularTailSpace) (hr : Tendsto r atTop (𝓝 r₀)) :
    Tendsto (fun n => circularInverseCorrection κ hκ (νp n) (νm n) η (m n) (hm n) (q n) (r n))
      atTop (𝓝 (circularInverseCorrection κ hκ μp μm η 1 (by omega) 0 r₀)) := by
  unfold circularInverseCorrection
  exact circularCorrection_free_tendsto κ hκ νp νm μp μm η hp hn m hm q δ hδ hδ0 hq hgap r r₀ hr

end DefocusingNLS

end OAI
