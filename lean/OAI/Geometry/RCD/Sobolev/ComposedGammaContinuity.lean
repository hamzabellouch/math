import OAI.Geometry.RCD.Sobolev.ComposedGammaPairingVariation

namespace OAI

/-! # Continuity of a weighted nonlinear gradient square

The weight only needs L² continuity, including at the initial heat time.
-/

open Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem composed_gamma_pairing_continuousAt {F : ℝ → SobolevSpace μ hQ}
    {W : ℝ → Lp ℝ 2 μ} {t : ℝ} (hF : ContinuousAt F t) (hW : ContinuousAt W t)
    (L : ℝ≥0) (hL : ∀ s, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (F s) x≤L)
    {b : ℝ → ℝ} {D : ℝ≥0} (hb : LipschitzWith D b)
    (E : ℝ≥0) (hE : ∀ a, |b a|≤E) :
    ContinuousAt (fun s => ∫ x, W s x*b (SobolevSpace.toLp μ hQ (F s) x)*
      localGamma μ hQ (F s) (F s) x ∂μ) t := by
  let G (s : ℝ) := (localGamma_memLp_of_bounded_gradient μ hQ (F s) (F s)
    L (hL s)).toLp (localGamma μ hQ (F s) (F s))
  let Q (s : ℝ) := boundedScalarProduct μ (SobolevSpace.toLp μ hQ (F s)) (G s) hb E hE
  have hGr (s : ℝ) : G s =ᵐ[μ] localGamma μ hQ (F s) (F s) := MemLp.coeFn_toLp _
  have hGb : ∀ᵐ x ∂μ, |G t x|≤(L^2:ℝ≥0) := by
    filter_upwards [hGr t,localGamma_self μ hQ (F t),hL t,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (F t))] with x hg hs hl hn
    rw [hg,hs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hn hl 2
  have hQc : ContinuousAt Q t := boundedScalarProduct_continuousAt μ hb E (L^2) hE hGb
    ((SobolevSpace.toLpCLM μ hQ).continuous.continuousAt.comp hF)
    (gammaL2_continuousAt μ hQ L hL hF)
  have hpair (s : ℝ) : inner ℝ (W s) (Q s) =
      ∫ x, W s x*b (SobolevSpace.toLp μ hQ (F s) x)*localGamma μ hQ (F s) (F s) x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [boundedScalarProduct_coe μ (SobolevSpace.toLp μ hQ (F s)) (G s) hb E hE,
      hGr s] with x hx hy
    change Q s x = _ at hx
    simp only [Real.inner_apply,hx,hy]
    ring
  simpa only [hpair] using hW.inner (𝕜:=ℝ) hQc

end RegularPointCoordinates

end

end OAI
