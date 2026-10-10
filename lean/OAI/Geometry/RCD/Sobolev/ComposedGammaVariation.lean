import OAI.Geometry.RCD.Coordinates.TwoFrozenPairingVariation
import OAI.Geometry.RCD.Harmonic.WeightedAffineComposition
import OAI.Geometry.RCD.Sobolev.GammaL2ContinuousAt
import OAI.Geometry.RCD.Harmonic.NonlinearPairingVariation

namespace OAI

/-! # Differentiating a scalar coefficient times a gradient square

The coefficient and energy density are paired in L². Two frozen scalar
derivatives and a controlled mixed increment justify the variation.
-/

open Filter MeasureTheory Asymptotics
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem composed_gamma_hasDerivAt {F : ℝ → SobolevSpace μ hQ}
    {V : SobolevSpace μ hQ} {t : ℝ} (hF : HasDerivAt F V t)
    (L : ℝ≥0) (hL : ∀ s, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (F s) x≤L)
    (θ : Lp ℝ ∞ μ) (w : Lp ℝ 2 μ) (hθ : θ =ᵐ[μ] w)
    (M : ℝ≥0) (hM : ∀ᵐ x ∂μ, |θ x|≤M)
    {b db : ℝ → ℝ} {D J : ℝ≥0} (hb : LipschitzWith D b)
    (hdb : LipschitzWith J db) (hd : ∀ a, HasDerivAt b (db a) a)
    (E : ℝ≥0) (hE : ∀ a, |b a|≤E) :
    HasDerivAt (fun s => ∫ x, θ x*b (SobolevSpace.toLp μ hQ (F s) x)*
      localGamma μ hQ (F s) (F s) x ∂μ)
      ((∫ x, θ x*db (SobolevSpace.toLp μ hQ (F t) x)*
        SobolevSpace.toLp μ hQ V x*localGamma μ hQ (F t) (F t) x ∂μ)+
       2*(∫ x, θ x*b (SobolevSpace.toLp μ hQ (F t) x)*
        localGamma μ hQ (F t) V x ∂μ)) t := by
  let P (s : ℝ) := SobolevSpace.toLp μ hQ (F s)
  let B (s : ℝ) := weightedAffineComposition μ θ w hb (P s)
  let G (s : ℝ) := (localGamma_memLp_of_bounded_gradient μ hQ (F s) (F s)
    L (hL s)).toLp (localGamma μ hQ (F s) (F s))
  have hGr (s : ℝ) : G s =ᵐ[μ] localGamma μ hQ (F s) (F s) := MemLp.coeFn_toLp _
  have hBr (s : ℝ) : B s =ᵐ[μ] fun x => θ x*b (P s x) :=
    weightedAffineComposition_coe μ θ w hθ hb (P s)
  have hP : HasDerivAt P (SobolevSpace.toLp μ hQ V) t :=
    (SobolevSpace.toLpCLM μ hQ).hasFDerivAt.comp_hasDerivAt t hF
  have hBig : (fun s => B s-B t) =O[𝓝 t] (fun s => s-t) :=
    (IsBigO.of_bound (‖lpMultiplier μ θ‖*D) (Eventually.of_forall fun s =>
      weightedAffineComposition_sub_norm_le μ θ w hb (P s) (P t))).trans hP.isBigO_sub
  have hGc : ContinuousAt G t := gammaL2_continuousAt μ hQ L hL hF.continuousAt
  let R := lpMultiplier μ θ (G t)
  have hRr : R =ᵐ[μ] fun x => θ x*localGamma μ hQ (F t) (F t) x := by
    filter_upwards [lpMultiplier_coe μ θ (G t),hGr t] with x hx hy
    exact hx.trans (by rw [hy])
  have hRb : ∀ᵐ x ∂μ, |R x|≤(M*L^2:ℝ≥0) := by
    filter_upwards [hRr,hM,hL t,localGamma_self μ hQ (F t),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (F t))]
      with x hr hm hl hg hn
    rw [hr,abs_mul,hg,abs_of_nonneg (sq_nonneg (SobolevSpace.minimalSlope μ hQ (F t) x))]
    exact mul_le_mul hm (pow_le_pow_left₀ hn hl 2) (sq_nonneg _) M.coe_nonneg
  have hRi : MemLp R ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable R) (M*L^2)
    (by simpa only [Real.norm_eq_abs,NNReal.coe_mul,NNReal.coe_pow] using hRb)
  let η := hRi.toLp R
  have hη : η =ᵐ[μ] R := hRi.coeFn_toLp
  have hηb : ∀ᵐ x ∂μ, |η x|≤(M*L^2:ℝ≥0) := by
    filter_upwards [hη,hRb] with x hx hy
    exact hx ▸ hy
  let T := lpMultiplier μ η ((centeredLipschitz hdb).compLp (sub_self _) (P t))+db 0 • R
  have hfixed : HasDerivAt (fun s => weightedIntegralPotential μ η
      (fun a => b a-b 0) (P s)) (inner ℝ T (SobolevSpace.toLp μ hQ V)) t := by
    have hh := (weightedIntegralPotential_affine_hasFDerivAt μ η R hη (M*L^2) hηb
      (fun a => (hd a).sub_const (b 0)) (sub_self _) hdb (P t)).comp_hasDerivAt t hP
    simpa only [innerSL_apply_apply] using! hh
  have hfun (s : ℝ) : inner ℝ (B s) (G t) =
      weightedIntegralPotential μ η (fun a => b a-b 0) (P s)+b 0*inner ℝ w (G t) := by
    change inner ℝ (lpMultiplier μ θ ((centeredLipschitz hb).compLp (sub_self _) (P s))+
      b 0 • w) (G t) = _
    rw [inner_add_left,real_inner_smul_left,←lpMultiplier_inner_symm,real_inner_comm]
    rw [inner_compLp_eq_weightedPotential μ R (P s) η hη (centeredLipschitz hb) (sub_self _)]
  have hleft : HasDerivAt (fun s => inner ℝ (B s) (G t))
      (inner ℝ T (SobolevSpace.toLp μ hQ V)) t := by
    simpa only [hfun] using hfixed.add_const (b 0*inner ℝ w (G t))
  have hBt : ∀ᵐ x ∂μ, ‖B t x‖≤(M*E:ℝ≥0) := by
    filter_upwards [hBr t,hM] with x hx hm
    rw [hx,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact mul_le_mul hm (hE _) (abs_nonneg _) M.coe_nonneg
  have hright : HasDerivAt (fun s => inner ℝ (B t) (G s))
      (2*weightedGamma μ hQ (B t) (F t) V) t := by
    have hh := ContinuousLinearMap.hasDerivAt_of_bilinear
      (B := weightedGammaCLM μ hQ (Lp.aestronglyMeasurable (B t)) hBt)
      (fun _ => hF) (fun _ => hF)
    change HasDerivAt (fun s => weightedGamma μ hQ (B t) (F s) (F s))
      (weightedGamma μ hQ (B t) (F t) V+weightedGamma μ hQ (B t) V (F t)) t at hh
    rw [weightedGamma_comm μ hQ (B t) V (F t)] at hh
    have heq : (fun s => inner ℝ (B t) (G s)) =
        (fun s => weightedGamma μ hQ (B t) (F s) (F s)) := by
      funext s
      exact (weightedGamma_eq_L2_inner μ hQ (F s) (F s) _ (B t)).symm
    rw [heq]
    convert hh using 1
    ring
  have hder := hasDerivAt_inner_of_two_frozen hBig hGc hleft hright
  have hval (s : ℝ) : inner ℝ (B s) (G s) =
      ∫ x, θ x*b (P s x)*localGamma μ hQ (F s) (F s) x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hBr s,hGr s] with x hx hy
    simp only [Real.inner_apply,hx,hy]
  have hprime : inner ℝ T (SobolevSpace.toLp μ hQ V) =
      ∫ x, θ x*db (P t x)*SobolevSpace.toLp μ hQ V x*
        localGamma μ hQ (F t) (F t) x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (lpMultiplier μ η ((centeredLipschitz hdb).compLp (sub_self _) (P t)))
        (db 0 • R), lpMultiplier_coe μ η ((centeredLipschitz hdb).compLp (sub_self _) (P t)),
      (centeredLipschitz hdb).coeFn_compLp (sub_self _) (P t),Lp.coeFn_smul (db 0) R,hη,hRr]
      with x ha hp hc hs hηx hr
    change T x = _ at ha
    simp only [Real.inner_apply,ha,Pi.add_apply,hp,hc,Function.comp_apply,hs,
      Pi.smul_apply,smul_eq_mul,hηx,hr]
    ring
  have hcross : weightedGamma μ hQ (B t) (F t) V =
      ∫ x, θ x*b (P t x)*localGamma μ hQ (F t) V x ∂μ :=
    integral_congr_ae ((hBr t).mono fun x hx => congrArg (fun a => a*localGamma μ hQ (F t) V x) hx)
  simpa only [hval,hprime,hcross] using hder

end RegularPointCoordinates

end

end OAI
