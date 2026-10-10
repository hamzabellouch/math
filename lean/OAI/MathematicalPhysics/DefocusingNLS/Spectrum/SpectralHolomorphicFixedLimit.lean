import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicSingularLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalFixedFirst
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalFixedSecond
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointMultiplicity

namespace OAI

/-! The actual holomorphic columns converge on a fixed exterior interval. -/

open Filter Topology Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_holomorphic_H_fixed_limit
    (ν m lam : ℕ → ℂ) (b : ℝ) (m₀ lam₀ : ℂ) (ell : ℕ)
    (hν : Tendsto ν atTop (𝓝 (2*Complex.I*(b : ℂ))))
    (hm : Tendsto m atTop (𝓝 m₀)) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re)
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L)
    (Y Z : ℕ → ℂ → ℝ → E₄)
    (hY : ∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (ν n) ((ell*(ell+10) : ℕ) : ℂ)
      (m n) n L (1,0) (Y n))
    (hZ : ∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (ν n) ((ell*(ell+10) : ℕ) : ℂ)
      (m n) n L (0,1) (Z n))
    (A : ℝ) (hA : 0 ≤ A)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hc : ∀ᶠ n in atTop, ∀ t ∈ Ici A,
      ‖spectralDiagonalCoefficient n (radialExteriorCanonical (ν n) n (m n) L t).1‖+
      ‖spectralCrossCoefficient n (radialExteriorCanonical (ν n) n (m n) L t).1‖ ≤ ε n) :
    TendstoUniformlyOn (fun n => Y n (lam n))
      (spectralFreeFirstColumn ell (spectralQ ell 1 b lam₀)) atTop (Ici A) ∧
    TendstoUniformlyOn (fun n => Z n (lam n))
      (spectralFreeSecondColumn ell (spectralQ ell (-1) b lam₀)) atTop (Ici A) := by
  let ν₀ : ℂ := 2*Complex.I*(b : ℂ)
  have hp : Tendsto (fun n => ν n-2*lam n) atTop
      (𝓝 ((ell : ℂ)-2*spectralQ ell 1 b lam₀)) := by
    convert hν.sub (hlam.const_mul 2) using 1
    congr 1
    unfold spectralQ
    push_cast
    ring
  have hn : Tendsto (fun n => star (ν n)-2*lam n) atTop
      (𝓝 ((ell : ℂ)-2*spectralQ ell (-1) b lam₀)) := by
    convert hν.star.sub (hlam.const_mul 2) using 1
    congr 1
    simp only [spectralQ,star_mul,star_ofNat,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  have hq (h : ℝ) : -1 < (spectralQ ell h b lam₀).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hlimY := canonical_circular_first_H_fixed_limit ν m
    (fun n => ν n-2*lam n) (fun n => star (ν n)-2*lam n)
    ν₀ m₀ ((ell : ℂ)-2*spectralQ ell (-1) b lam₀) (spectralQ ell 1 b lam₀) ell
    hν hm hp hn (hq 1) δ L hδ hsmall hX (fun n => Y n (lam n))
    (hY.mono (fun n hy t ht => hy.1 (lam n) t ht))
    (hY.mono (fun n hy J => hy.2.2.2 (lam n) J)) A hA ε hε hεlim hc
  have hlimZ := canonical_circular_second_H_fixed_limit ν m
    (fun n => ν n-2*lam n) (fun n => star (ν n)-2*lam n)
    ν₀ m₀ ((ell : ℂ)-2*spectralQ ell 1 b lam₀) (spectralQ ell (-1) b lam₀) ell
    hν hm hp hn (hq (-1)) δ L hδ hsmall hX (fun n => Z n (lam n))
    (hZ.mono (fun n hz t ht => hz.1 (lam n) t ht))
    (hZ.mono (fun n hz J => hz.2.2.2 (lam n) J)) A hA ε hε hεlim hc
  exact ⟨hlimY,hlimZ⟩

end DefocusingNLS

end OAI
