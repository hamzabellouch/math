import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicFreeLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeColumnNormalization
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalRobinLimit

namespace OAI

/-! The actual Robin matrix converges to the matrix of the explicit free H basis. -/

open Filter Topology Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_canonical_holomorphic_H_robin_limit_with_det
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
      let νp := 2*Complex.I*(b : ℂ)-2*lam₀
      let νm := star (2*Complex.I*(b : ℂ))-2*lam₀
      let U₀ := spectralPhysicalPair νp νm
        (spectralFreeFirstColumn ell (spectralQ ell 1 b lam₀)) R
      let V₀ := spectralPhysicalPair νp νm
        (spectralFreeSecondColumn ell (spectralQ ell (-1) b lam₀)) R
      Tendsto (fun n => spectralJetRobin
        (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Y n (lam n)) R)
        (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Z n (lam n)) R)) atTop
          (𝓝 (spectralJetRobin U₀ V₀)) ∧
      spectralValueDet (spectralPhysicalValueMap U₀) (spectralPhysicalValueMap V₀) ≠ 0 ∧
      ∀ᶠ n in atTop, spectralValueDet
        (spectralPhysicalValueMap (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Y n (lam n)) R))
        (spectralPhysicalValueMap (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Z n (lam n)) R)) ≠ 0 := by
  obtain ⟨Y,Z,hYZ,T,hT,_hLT,hy,hz⟩ := exists_canonical_holomorphic_H_limit
    ν m lam b m₀ lam₀ ell hν hm hlam hm₀ hlam₀ δ L hδ hsmall hX
  have hq (h : ℝ) : -1 < (spectralQ ell h b lam₀).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hd := spectralPhysicalValueDet_eventually_ne_zero
    (2*Complex.I*(b : ℂ)-2*lam₀) (star (2*Complex.I*(b : ℂ))-2*lam₀)
    (spectralFreeFirstColumn ell (spectralQ ell 1 b lam₀))
    (spectralFreeSecondColumn ell (spectralQ ell (-1) b lam₀))
    (spectralFreeFirstColumn_tendsto ell _ (hq 1))
    (spectralFreeSecondColumn_tendsto ell _ (hq (-1)))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop T)
  obtain ⟨R,hR₀,hR,hlogR,hdR⟩ :=
    ((eventually_ge_atTop R₀).and ((eventually_ge_atTop (1 : ℝ)).and (hlog.and hd))).exists
  have hp := hν.sub (hlam.const_mul 2)
  have hn := hν.star.sub (hlam.const_mul 2)
  have hUR := spectralPhysicalPair_tendsto _ _ _ _ _ _ R hp hn (hy.tendsto_at hlogR)
  have hVR := spectralPhysicalPair_tendsto _ _ _ _ _ _ R hp hn (hz.tendsto_at hlogR)
  have hdlim := spectralValueDet_tendsto _ _ _ _
    (spectralPhysicalValueMap.continuous.continuousAt.tendsto.comp hUR)
    (spectralPhysicalValueMap.continuous.continuousAt.tendsto.comp hVR)
  exact ⟨R,hR₀,hR,Y,Z,hYZ,spectralJetRobin_tendsto _ _ _ _ hUR hVR hdR,hdR,
    hdlim.eventually (eventually_ne_nhds hdR)⟩

theorem exists_canonical_holomorphic_H_robin_limit
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
      let νp := 2*Complex.I*(b : ℂ)-2*lam₀
      let νm := star (2*Complex.I*(b : ℂ))-2*lam₀
      let U₀ := spectralPhysicalPair νp νm
        (spectralFreeFirstColumn ell (spectralQ ell 1 b lam₀)) R
      let V₀ := spectralPhysicalPair νp νm
        (spectralFreeSecondColumn ell (spectralQ ell (-1) b lam₀)) R
      Tendsto (fun n => spectralJetRobin
        (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Y n (lam n)) R)
        (spectralPhysicalPair (ν n-2*lam n) (star (ν n)-2*lam n) (Z n (lam n)) R)) atTop
          (𝓝 (spectralJetRobin U₀ V₀)) ∧
      spectralValueDet (spectralPhysicalValueMap U₀) (spectralPhysicalValueMap V₀) ≠ 0 := by
  obtain ⟨R,hR₀,hR,Y,Z,hYZ,hlim,hd,_⟩ := exists_canonical_holomorphic_H_robin_limit_with_det
    ν m lam b m₀ lam₀ ell hν hm hlam hm₀ hlam₀ δ L R₀ hδ hsmall hX
  exact ⟨R,hR₀,hR,Y,Z,hYZ,hlim,hd⟩

end DefocusingNLS

end OAI
