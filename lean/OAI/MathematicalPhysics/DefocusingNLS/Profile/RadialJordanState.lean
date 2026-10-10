import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialJordanChannels
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicSmoothness

namespace OAI

/-! The physical first-order equation of a radial Jordan chain. -/

open scoped ContDiff
namespace DefocusingNLS

theorem harmonicRadialSourcePair_hasDerivAt (a b : ℝ) (m : ℕ)
    (Q f g F G : ℝ → ℂ) (eta lam : ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (heq : IsHarmonicRadialSourcePair a b m Q eta lam f g F G)
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (harmonicRadialState f g)
      (spectralPhysicalCircularField (-2 * (a : ℂ) + 2 * Complex.I * (b : ℂ) - 2 * lam)
        (-2 * (a : ℂ) - 2 * Complex.I * (b : ℂ) - 2 * lam) eta m (Q r) r
        (harmonicRadialState f g r) +
          ((0, -Complex.I * F r), (0, Complex.I * G r))) r := by
  have hfd := ((hf.deriv' : ContDiff ℝ 1 (deriv f)).differentiable one_ne_zero r).hasDerivAt
  have hgd := ((hg.deriv' : ContDiff ℝ 1 (deriv g)).differentiable one_ne_zero r).hasDerivAt
  have hd := (((hf.differentiable (by norm_num) r).hasDerivAt.prodMk hfd).prodMk
    ((hg.differentiable (by norm_num) r).hasDerivAt.prodMk hgd))
  apply hd.congr_deriv
  obtain ⟨hp, hm⟩ := heq r hr
  apply Prod.ext <;> apply Prod.ext
  · simp only [Prod.fst_add, add_zero, harmonicRadialState, spectralPhysicalCircularField]
  · dsimp only [harmonicRadialState, spectralPhysicalCircularField,
      spectralDiagonalCoefficient, spectralCrossCoefficient, Prod.fst_add, Prod.snd_add]
    push_cast at hp ⊢
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring)) Complex.I * hp
  · simp only [Prod.snd_add, Prod.fst_add, add_zero, harmonicRadialState,
      spectralPhysicalCircularField]
  · dsimp only [harmonicRadialState, spectralPhysicalCircularField,
      spectralDiagonalCoefficient, spectralCrossCoefficient, Prod.fst_add, Prod.snd_add]
    push_cast at hm ⊢
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring)) -Complex.I * hm

end DefocusingNLS

end OAI
