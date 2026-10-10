import OAI.NumberTheory.CubicMoment.Transform.MetaplecticVoronoiStrip
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticStripGrowth

namespace OAI

/-! The internal strip-growth property can be supplied either by the
original published auxiliary estimates or directly by the Voronoi formula.
The latter route removes those auxiliary hypotheses from the main results. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

def MetaplecticPolynomialGrowth (F : Eisenstein → ℂ → ℂ) : Prop :=
  ∀ r : Eisenstein, primary r → Squarefree r → ∀ ε : ℝ, 0 < ε →
    MetaplecticStripPolynomial (F r) (1/2+ε) 2

lemma metaplectic_polynomial_growth_of_published {F Ψ Z : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZ : HeathBrownZBound Z)
    (hfac : HeathBrownZFactorization Ψ Z) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) : MetaplecticPolynomialGrowth F :=
  fun _ hr hs _ hε => metaplectic_strip_polynomial_of_published hF hZ hfac hdiv hpart hr hs hε

lemma metaplectic_continuation_unique {F G : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hG : MetaplecticContinuation G)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    {s : ℂ} (hs : (1/2:ℝ) < s.re) (hsp : s ≠ 5/6) : F r s = G r s := by
  obtain ⟨hFr,f,hf,hef⟩ := hF r hr hsr
  obtain ⟨hGr,g,hg,heg⟩ := hG r hr hsr
  have hopen : IsOpen {z : ℂ | (1/2:ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq := (hf.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hopen) (convex_halfSpace_re_gt (1/2)).isPreconnected
    (z₀ := (2:ℂ)) (by norm_num)
  have he : f s = g s := by
    apply heq ?_ hs
    have hn : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    have hzp : z ≠ (5/6:ℂ) := by intro h; subst z; norm_num at hz
    have hzhalf : (1/2:ℝ) < z.re := by linarith
    have h1 := hef z hzhalf hzp
    have h2 := heg z hzhalf hzp
    rw [hFr z hz] at h1
    rw [hGr z hz] at h2
    exact add_right_cancel (h1.symm.trans h2)
  rw [hef s hs hsp,heg s hs hsp,he]

theorem metaplectic_polynomial_growth_of_voronoi
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {F : Eisenstein → ℂ → ℂ} (hF : MetaplecticContinuation F) :
    MetaplecticPolynomialGrowth F := by
  intro r hr hsr ε hε
  obtain ⟨C,hC,N,hbound⟩ := metaplectic_strip_polynomial_of_voronoi hV hr hsr hε
  refine ⟨C,hC,N,?_⟩
  intro σ hσ t ht
  have hs : (1/2:ℝ) < ((σ:ℂ)+(t:ℂ)*Complex.I).re := by simp; linarith [hσ.1]
  have hsp : (σ:ℂ)+(t:ℂ)*Complex.I ≠ (5/6:ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hi
    norm_num at hi
    rw [hi,abs_zero] at ht
    norm_num at ht
  rw [metaplectic_continuation_unique hF (metaplecticContinuation_of_voronoi hV) hr hsr hs hsp]
  exact hbound σ hσ t ht

end CubicFirstMoment

end

end OAI
