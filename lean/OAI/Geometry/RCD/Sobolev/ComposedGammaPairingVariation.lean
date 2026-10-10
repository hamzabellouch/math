import OAI.Geometry.RCD.Sobolev.ComposedGammaVariation
import OAI.Geometry.RCD.Harmonic.BoundedScalarProduct

namespace OAI

/-! # Variation of a weighted nonlinear gradient square

Only the original Sobolev path and the L² weight are differentiated.
-/

open Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem composed_gamma_pairing_hasDerivAt {F : ℝ → SobolevSpace μ hQ}
    {V : SobolevSpace μ hQ} {W : ℝ → Lp ℝ 2 μ} {W' : Lp ℝ 2 μ} {t : ℝ}
    (hF : HasDerivAt F V t) (hW : HasDerivAt W W' t)
    (L : ℝ≥0) (hL : ∀ s, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (F s) x≤L)
    (θ : Lp ℝ ∞ μ) (hθ : θ =ᵐ[μ] W t) (M : ℝ≥0) (hM : ∀ᵐ x ∂μ, |θ x|≤M)
    {b db : ℝ → ℝ} {D J : ℝ≥0} (hb : LipschitzWith D b)
    (hdb : LipschitzWith J db) (hd : ∀ a, HasDerivAt b (db a) a)
    (E : ℝ≥0) (hE : ∀ a, |b a|≤E) :
    HasDerivAt (fun s => ∫ x, W s x*b (SobolevSpace.toLp μ hQ (F s) x)*
      localGamma μ hQ (F s) (F s) x ∂μ)
      ((∫ x, W' x*b (SobolevSpace.toLp μ hQ (F t) x)*localGamma μ hQ (F t) (F t) x ∂μ)+
       (∫ x, W t x*db (SobolevSpace.toLp μ hQ (F t) x)*
        SobolevSpace.toLp μ hQ V x*localGamma μ hQ (F t) (F t) x ∂μ)+
       2*(∫ x, W t x*b (SobolevSpace.toLp μ hQ (F t) x)*localGamma μ hQ (F t) V x ∂μ)) t := by
  let G (s : ℝ) := (localGamma_memLp_of_bounded_gradient μ hQ (F s) (F s)
    L (hL s)).toLp (localGamma μ hQ (F s) (F s))
  let Q (s : ℝ) := boundedScalarProduct μ (SobolevSpace.toLp μ hQ (F s)) (G s) hb E hE
  have hGr (s : ℝ) : G s =ᵐ[μ] localGamma μ hQ (F s) (F s) := MemLp.coeFn_toLp _
  have hQr (s : ℝ) : Q s =ᵐ[μ] fun x => b (SobolevSpace.toLp μ hQ (F s) x)*
      localGamma μ hQ (F s) (F s) x := by
    filter_upwards [boundedScalarProduct_coe μ (SobolevSpace.toLp μ hQ (F s)) (G s) hb E hE,
      hGr s] with x hx hy
    exact hx.trans (by rw [hy])
  have hGb : ∀ᵐ x ∂μ, |G t x|≤(L^2:ℝ≥0) := by
    filter_upwards [hGr t,localGamma_self μ hQ (F t),hL t,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (F t))] with x hg hs hl hn
    rw [hg,hs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hn hl 2
  have hQc : ContinuousAt Q t := boundedScalarProduct_continuousAt μ hb E (L^2) hE hGb
    ((SobolevSpace.toLpCLM μ hQ).continuous.continuousAt.comp hF.continuousAt)
    (gammaL2_continuousAt μ hQ L hL hF.continuousAt)
  have hpair (v : Lp ℝ 2 μ) (s : ℝ) : inner ℝ v (Q s) =
      ∫ x, v x*b (SobolevSpace.toLp μ hQ (F s) x)*localGamma μ hQ (F s) (F s) x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQr s] with x hx
    simp only [Real.inner_apply,hx]
    ring
  have hfixed := composed_gamma_hasDerivAt μ hQ hF L hL θ (W t) hθ M hM hb hdb hd E hE
  have hfixed' : HasDerivAt (fun s => inner ℝ (W t) (Q s))
      ((∫ x, W t x*db (SobolevSpace.toLp μ hQ (F t) x)*
        SobolevSpace.toLp μ hQ V x*localGamma μ hQ (F t) (F t) x ∂μ)+
       2*(∫ x, W t x*b (SobolevSpace.toLp μ hQ (F t) x)*localGamma μ hQ (F t) V x ∂μ)) t := by
    have hval : (fun s => inner ℝ (W t) (Q s)) =
        (fun s => ∫ x, θ x*b (SobolevSpace.toLp μ hQ (F s) x)*
          localGamma μ hQ (F s) (F s) x ∂μ) := by
      funext s
      rw [hpair]
      exact integral_congr_ae (hθ.mono fun x hx => by dsimp only; rw [hx])
    rw [hval]
    convert hfixed using 1
    congr 1
    · apply integral_congr_ae
      filter_upwards [hθ] with x hx
      rw [hx]
    · congr 1
      apply integral_congr_ae
      filter_upwards [hθ] with x hx
      rw [hx]
  have hh := hasDerivAt_inner_of_frozen hW hQc hfixed'
  simpa only [hpair,add_assoc] using hh

end RegularPointCoordinates

end

end OAI
