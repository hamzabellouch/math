import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFieldParameterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralResolventAnalytic

namespace OAI

/-! Continuity of the actual weighted correction resolvent follows from
operator-norm convergence of its coefficient field and invertibility at the
free limit. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "End₄" => CircularTailSpace →L[ℂ] CircularTailSpace

theorem spectralCorrectionInverse_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (B : ℕ → E →L[ℂ] E) (B₀ : E →L[ℂ] E)
    (hB : Tendsto B atTop (𝓝 B₀)) (hu : IsUnit (1-T*B₀)) :
    Tendsto (fun n => Ring.inverse (1-T*B n)) atTop (𝓝 (Ring.inverse (1-T*B₀))) := by
  have hi : ContinuousAt (Ring.inverse : (E →L[ℂ] E) → E →L[ℂ] E) (1-T*B₀) := by
    simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
  exact hi.tendsto.comp (tendsto_const_nhds.sub (tendsto_const_nhds.mul hB))

theorem circularCorrection_free_tendsto (κ : ℝ) (hκ : 0 < κ)
    (νp νm : ℕ → ℂ) (μp μm η : ℂ)
    (hp : Tendsto νp atTop (𝓝 μp)) (hn : Tendsto νm atTop (𝓝 μm))
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n) (q : ℕ → ℝ →ᵇ ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hq : ∀ᶠ n in atTop, ∀ t,
      ‖spectralDiagonalCoefficient (m n) (q n t)‖+‖spectralCrossCoefficient (m n) (q n t)‖ ≤ δ n)
    (hgap : circularFieldBound μp μm η 1 ‖(0 : ℝ →ᵇ ℂ)‖ < κ)
    (r : ℕ → CircularTailSpace) (r₀ : CircularTailSpace) (hr : Tendsto r atTop (𝓝 r₀)) :
    Tendsto (fun n =>
      Ring.inverse (1-circularTailCLM κ hκ*circularFieldOperator (νp n) (νm n) η (m n) (hm n) (q n))
        (circularTailCLM κ hκ (r n))) atTop
      (𝓝 (Ring.inverse (1-circularTailCLM κ hκ*circularFieldOperator μp μm η 1 (by omega) 0)
        (circularTailCLM κ hκ r₀))) := by
  let : NormedAddCommGroup CircularTailSpace := inferInstance
  let : NormedSpace ℂ CircularTailSpace := inferInstance
  let : CompleteSpace CircularTailSpace := inferInstance
  have hB := circularFieldOperator_free_tendsto νp νm μp μm η hp hn m hm q δ hδ hδ0 hq
  have hi := spectralCorrectionInverse_tendsto (circularTailCLM κ hκ) _ _ hB
    (circularCorrection_isUnit κ hκ μp μm η 1 (by omega) 0 hgap)
  have he : Continuous (fun p : End₄ × CircularTailSpace => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact he.continuousAt.tendsto.comp
    (hi.prodMk_nhds ((circularTailCLM κ hκ).continuous.continuousAt.tendsto.comp hr))

end DefocusingNLS

end OAI
