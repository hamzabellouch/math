import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicSingularLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalFreeFirstLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalFreeSecondLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointMultiplicity

namespace OAI

/-! The actual holomorphic columns converge to the two explicit free H columns. -/

open Filter Topology Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_canonical_holomorphic_H_limit
    (ν m lam : ℕ → ℂ) (b : ℝ) (m₀ lam₀ : ℂ) (ell : ℕ)
    (hν : Tendsto ν atTop (𝓝 (2*Complex.I*(b : ℂ))))
    (hm : Tendsto m atTop (𝓝 m₀)) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hm₀ : m₀ ≠ 0) (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re)
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L) :
    ∃ Y Z : ℕ → ℂ → ℝ → E₄,
      (∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (ν n) ((ell*(ell+10) : ℕ) : ℂ)
        (m n) n L (1,0) (Y n) ∧
        IsCanonicalHolomorphicColumn (ν n) ((ell*(ell+10) : ℕ) : ℂ)
          (m n) n L (0,1) (Z n)) ∧
      ∃ T : ℝ, 0 ≤ T ∧ L ≤ T ∧
        TendstoUniformlyOn (fun n => Y n (lam n))
          (spectralFreeFirstColumn ell (spectralQ ell 1 b lam₀)) atTop (Ici T) ∧
        TendstoUniformlyOn (fun n => Z n (lam n))
          (spectralFreeSecondColumn ell (spectralQ ell (-1) b lam₀)) atTop (Ici T) := by
  let η : ℂ := ((ell*(ell+10) : ℕ) : ℂ)
  let ν₀ : ℂ := 2*Complex.I*(b : ℂ)
  obtain ⟨Y,hY,_⟩ := exists_canonical_holomorphic_singular_limit ν m lam ν₀ m₀ lam₀ η
    hν hm hlam hm₀ δ L hδ hsmall hX (1,0)
  obtain ⟨Z,hZ,_⟩ := exists_canonical_holomorphic_singular_limit ν m lam ν₀ m₀ lam₀ η
    hν hm hlam hm₀ δ L hδ hsmall hX (0,1)
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
  obtain ⟨TY,hTY,hLTY,hlimY⟩ := canonical_circular_first_H_limit ν m
    (fun n => ν n-2*lam n) (fun n => star (ν n)-2*lam n)
    ν₀ m₀ ((ell : ℂ)-2*spectralQ ell (-1) b lam₀) (spectralQ ell 1 b lam₀) ell
    hν hm hp hn (hq 1) δ L hδ hsmall hX (fun n => Y n (lam n))
    (hY.mono (fun n hy t ht => hy.1 (lam n) t ht))
    (hY.mono (fun n hy J => hy.2.2.2 (lam n) J))
  obtain ⟨TZ,hTZ,hLTZ,hlimZ⟩ := canonical_circular_second_H_limit ν m
    (fun n => ν n-2*lam n) (fun n => star (ν n)-2*lam n)
    ν₀ m₀ ((ell : ℂ)-2*spectralQ ell 1 b lam₀) (spectralQ ell (-1) b lam₀) ell
    hν hm hp hn (hq (-1)) δ L hδ hsmall hX (fun n => Z n (lam n))
    (hZ.mono (fun n hz t ht => hz.1 (lam n) t ht))
    (hZ.mono (fun n hz J => hz.2.2.2 (lam n) J))
  refine ⟨Y,Z,hY.and hZ,max TY TZ,hTY.trans (le_max_left _ _),
    hLTY.trans (le_max_left _ _),?_,?_⟩
  · rw [Metric.tendstoUniformlyOn_iff] at hlimY ⊢
    intro ε hε
    filter_upwards [hlimY ε hε] with n hn t ht
    exact hn t (show TY ≤ t from (le_max_left TY TZ).trans ht)
  · rw [Metric.tendstoUniformlyOn_iff] at hlimZ ⊢
    intro ε hε
    filter_upwards [hlimZ ε hε] with n hn t ht
    exact hn t (show TZ ≤ t from (le_max_right TY TZ).trans ht)

end DefocusingNLS

end OAI
