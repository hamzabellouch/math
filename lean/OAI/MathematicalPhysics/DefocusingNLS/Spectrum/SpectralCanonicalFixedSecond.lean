import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalFreeSecondLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularTailLimit

namespace OAI

/-! Convergence of the canonical second column at a fixed exterior endpoint. -/

open Filter Topology Set Polynomial
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_circular_second_H_fixed_limit
    (ν m νp νm : ℕ → ℂ) (ν₀ m₀ νp₀ q : ℂ) (ell : ℕ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (hp : Tendsto νp atTop (𝓝 νp₀))
    (hn : Tendsto νm atTop (𝓝 ((ell : ℂ)-2*q))) (hq : -1 < q.re)
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L)
    (W : ℕ → ℝ → E₄)
    (hW : ∀ᶠ n in atTop, ∀ t, 0 ≤ t → HasDerivAt (W n)
      (circularLeadingField t (W n t)+circularBoundedField (νp n) (νm n)
        ((ell*(ell+10) : ℕ) : ℂ) n (radialExteriorCanonical (ν n) n (m n) L t).1
          (W n t)) t)
    (heW : ∀ᶠ n in atTop, ∀ J : ℕ, ∃ k : ℕ, J ≤ k ∧ ∃ u : CircularTailSpace,
      ∀ t, 0 ≤ t → W n t=circularPolynomialJet
        (spectralOutgoingPolynomial (νp n) (νm n) ((ell*(ell+10) : ℕ) : ℂ) n
          (radialExteriorExpansion (ν n) n (m n) k) (0,1) k) t+
            circularUnweight (2*(k : ℝ)) u t)
    (A : ℝ) (hA : 0 ≤ A)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hc : ∀ᶠ n in atTop, ∀ t ∈ Ici A,
      ‖spectralDiagonalCoefficient n (radialExteriorCanonical (ν n) n (m n) L t).1‖+
      ‖spectralCrossCoefficient n (radialExteriorCanonical (ν n) n (m n) L t).1‖ ≤ ε n) :
    TendstoUniformlyOn W (spectralFreeSecondColumn ell q) atTop (Ici A) := by
  obtain ⟨T,_hT,_hLT,hlim⟩ := canonical_circular_second_H_limit
    ν m νp νm ν₀ m₀ νp₀ q ell hν hm hp hn hq δ L hδ hsmall hX W hW heW
  apply circularSolutions_tail_uniform_limit νp νm
    νp₀ ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
    hp hn id (eventually_ge_atTop 1)
    (fun n t => (radialExteriorCanonical (ν n) n (m n) L t).1)
    ε hε hεlim A T W (spectralFreeSecondColumn ell q) _ _ hc hlim
  · exact hW.mono (fun n h t ht => h t (hA.trans ht))
  · exact fun t _ => spectralFreeSecondColumn_hasDerivAt ell q νp₀ hq t

end DefocusingNLS

end OAI
