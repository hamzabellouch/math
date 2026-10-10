import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalBasis
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicHRobinLimit

namespace OAI

/-! The limiting canonical physical columns are the H basis used at the core. -/

open Filter Topology Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFreeExponent (ell : ℕ) (h b : ℝ) (ζ : ℂ) :
    (ell : ℂ)-2*spectralQ ell h b ζ=2*(h : ℂ)*Complex.I*(b : ℂ)-2*ζ := by
  unfold spectralQ
  ring

theorem spectralFreePhysicalPair_first (ell : ℕ) (b : ℝ) (ζ : ℂ) (r : ℝ) :
    spectralPhysicalPair (2*Complex.I*(b : ℂ)-2*ζ)
      (star (2*Complex.I*(b : ℂ))-2*ζ)
      (spectralFreeFirstColumn ell (spectralQ ell 1 b ζ)) r=
      spectralFreePositivePhysical ell b ζ r := by
  have he : (ell : ℂ)-2*spectralQ ell 1 b ζ=2*Complex.I*(b : ℂ)-2*ζ := by
    simpa only [Complex.ofReal_one,mul_one] using spectralFreeExponent ell 1 b ζ
  rw [spectralFreePositivePhysical,he]
  apply Prod.ext
  · rfl
  · simp [spectralPhysicalPair,spectralFreeFirstColumn,spectralPhysicalJet]

theorem spectralFreePhysicalPair_second (ell : ℕ) (b : ℝ) (ζ : ℂ) (r : ℝ) :
    spectralPhysicalPair (2*Complex.I*(b : ℂ)-2*ζ)
      (star (2*Complex.I*(b : ℂ))-2*ζ)
      (spectralFreeSecondColumn ell (spectralQ ell (-1) b ζ)) r=
      spectralFreeNegativePhysical ell b ζ r := by
  have he : (ell : ℂ)-2*spectralQ ell (-1) b ζ=star (2*Complex.I*(b : ℂ))-2*ζ := by
    rw [spectralFreeExponent]
    simp only [Complex.ofReal_neg,Complex.ofReal_one,Complex.star_def,map_mul,map_ofNat,
      Complex.conj_I,Complex.conj_ofReal]
    ring
  rw [spectralFreeNegativePhysical_eq,he]
  apply Prod.ext
  · simp [spectralPhysicalPair,spectralFreeSecondColumn,spectralPhysicalJet]
  · rfl


theorem exists_canonical_freePhysical_robin_limit_with_det
    (ν m lam : ℕ → ℂ) (b : ℝ) (m₀ lam₀ : ℂ) (ell : ℕ)
    (hν : Tendsto ν atTop (𝓝 (2*Complex.I*(b : ℂ))))
    (hm : Tendsto m atTop (𝓝 m₀)) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hm₀ : m₀ ≠ 0) (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re)
    (δ L R₀ : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L) :
    ∃ R : ℝ, R₀ ≤ R ∧ 1 ≤ R ∧ ∃ Y Z : ℕ → ℂ → ℝ → E₄,
      (∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (ν n) ((ell*(ell+10) : ℕ) : ℂ)
        (m n) n L (1,0) (Y n) ∧
        IsCanonicalHolomorphicColumn (ν n) ((ell*(ell+10) : ℕ) : ℂ)
          (m n) n L (0,1) (Z n)) ∧
      Tendsto (fun n => spectralJetRobin
        (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Y n (lam n)) R)
        (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Z n (lam n)) R)) atTop
          (𝓝 (spectralJetRobin (spectralFreePositivePhysical ell b lam₀ R)
            (spectralFreeNegativePhysical ell b lam₀ R))) ∧
      spectralValueDet (spectralPhysicalValueMap (spectralFreePositivePhysical ell b lam₀ R))
        (spectralPhysicalValueMap (spectralFreeNegativePhysical ell b lam₀ R)) ≠ 0 ∧
      ∀ᶠ n in atTop, spectralValueDet
        (spectralPhysicalValueMap (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Y n (lam n)) R))
        (spectralPhysicalValueMap (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Z n (lam n)) R)) ≠ 0 := by
  obtain ⟨R,hR₀,hR,Y,Z,hYZ,hlim,hdet,hdn⟩ := exists_canonical_holomorphic_H_robin_limit_with_det
    ν m lam b m₀ lam₀ ell hν hm hlam hm₀ hlam₀ δ L R₀ hδ hsmall hX
  refine ⟨R,hR₀,hR,Y,Z,hYZ,?_,?_,hdn⟩
  · simpa only [spectralFreePhysicalPair_first,spectralFreePhysicalPair_second] using hlim
  · simpa only [spectralFreePhysicalPair_first,spectralFreePhysicalPair_second] using hdet

theorem exists_canonical_freePhysical_robin_limit
    (ν m lam : ℕ → ℂ) (b : ℝ) (m₀ lam₀ : ℂ) (ell : ℕ)
    (hν : Tendsto ν atTop (𝓝 (2*Complex.I*(b : ℂ))))
    (hm : Tendsto m atTop (𝓝 m₀)) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hm₀ : m₀ ≠ 0) (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re)
    (δ L R₀ : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L) :
    ∃ R : ℝ, R₀ ≤ R ∧ 1 ≤ R ∧ ∃ Y Z : ℕ → ℂ → ℝ → E₄,
      (∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (ν n) ((ell*(ell+10) : ℕ) : ℂ)
        (m n) n L (1,0) (Y n) ∧
        IsCanonicalHolomorphicColumn (ν n) ((ell*(ell+10) : ℕ) : ℂ)
          (m n) n L (0,1) (Z n)) ∧
      Tendsto (fun n => spectralJetRobin
        (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Y n (lam n)) R)
        (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Z n (lam n)) R)) atTop
          (𝓝 (spectralJetRobin (spectralFreePositivePhysical ell b lam₀ R)
            (spectralFreeNegativePhysical ell b lam₀ R))) ∧
      spectralValueDet (spectralPhysicalValueMap (spectralFreePositivePhysical ell b lam₀ R))
        (spectralPhysicalValueMap (spectralFreeNegativePhysical ell b lam₀ R)) ≠ 0 := by
  obtain ⟨R,hR₀,hR,Y,Z,hYZ,hlim,hd,_⟩ := exists_canonical_freePhysical_robin_limit_with_det
    ν m lam b m₀ lam₀ ell hν hm hlam hm₀ hlam₀ δ L R₀ hδ hsmall hX
  exact ⟨R,hR₀,hR,Y,Z,hYZ,hlim,hd⟩

end DefocusingNLS

end OAI
