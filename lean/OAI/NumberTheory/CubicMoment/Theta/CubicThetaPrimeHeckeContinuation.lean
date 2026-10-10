import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeHeckeRelation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierParity

namespace OAI

/-! The local three-frequency identity holds for the actual meromorphic
continuation, hence for its holomorphic pole-cleared representative. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaPrimeNormPower_analytic {p : Eisenstein} (hp : primaryPrime p) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (norm p:ℂ)^(-z)) s := by
  let _ : NeZero (norm p:ℂ) := ⟨Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero hp.2.ne_zero).ne'⟩
  exact ((differentiable_const_cpow_of_neZero (norm p:ℂ)).analyticAt _).comp
    (f:=fun z : ℂ => -z) (x:=s) analyticAt_id.neg

lemma cubicThetaPrimeFirstFactor_analytic {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (s : ℂ) : AnalyticAt ℂ (fun z => cubicThetaPrimeFirstFactor p z h) s := by
  exact analyticAt_const.mul (cubicThetaPrimeNormPower_analytic hp s)

theorem cubicThetaFrequencyContinuation_primeHecke_germ {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) {s : ℂ} (hs : 1<s.re) :
    cubicThetaFrequencyContinuation (p^3*h)=ᶠ[𝓝[≠] s]
      (fun z => (1+(norm p:ℂ)^3*((norm p:ℂ)^(-z))^3)*cubicThetaFrequencyContinuation h z-
        cubicThetaPrimeFirstFactor p z h*cubicThetaFrequencyContinuation (p*h) z) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  have hph : p*h≠0 := mul_ne_zero hp.2.ne_zero hh0
  have hp3h : p^3*h≠0 := mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) hh0
  have hrhs : MeromorphicOn (fun z =>
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-z))^3)*cubicThetaFrequencyContinuation h z-
        cubicThetaPrimeFirstFactor p z h*cubicThetaFrequencyContinuation (p*h) z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (((analyticAt_const.add (analyticAt_const.mul
        ((cubicThetaPrimeNormPower_analytic hp z).pow 3))).meromorphicAt.mul
          (cubicThetaFrequencyContinuation_meromorphic hh0 hz)).sub
      ((cubicThetaPrimeFirstFactor_analytic hp h z).meromorphicAt.mul
        (cubicThetaFrequencyContinuation_meromorphic hph hz)))
  apply cubicThetaMeromorphic_identity
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic hp3h hz)
    hrhs (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by change 1<(4:ℂ).re; norm_num) hs
  have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right _ hz,cubicThetaFrequencyContinuation_right _ hz,
    cubicThetaFrequencyContinuation_right _ hz]
  exact cubicThetaFrequencyDirichlet_primeHecke hp (by linarith) h hh

theorem cubicThetaRegularizedFrequency_primeHecke {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) {s : ℂ} (hs : 1<s.re) :
    cubicThetaRegularizedFrequency (p^3*h) s=
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-s))^3)*cubicThetaRegularizedFrequency h s-
        cubicThetaPrimeFirstFactor p s h*cubicThetaRegularizedFrequency (p*h) s := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  have hph : p*h≠0 := mul_ne_zero hp.2.ne_zero hh0
  have hp3h : p^3*h≠0 := mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) hh0
  have he : cubicThetaRegularizedFrequency (p^3*h)=ᶠ[𝓝[≠] s]
      (fun z => (1+(norm p:ℂ)^3*((norm p:ℂ)^(-z))^3)*cubicThetaRegularizedFrequency h z-
        cubicThetaPrimeFirstFactor p z h*cubicThetaRegularizedFrequency (p*h) z) := by
    filter_upwards [cubicThetaRegularizedFrequency_germ hp3h hs,
      cubicThetaRegularizedFrequency_germ hh0 hs,cubicThetaRegularizedFrequency_germ hph hs,
      cubicThetaFrequencyContinuation_primeHecke_germ hp h hh hs] with z hz3 hz0 hz1 hz
    rw [hz3,hz0,hz1,hz]
    ring
  have hleft := (cubicThetaRegularizedFrequency_analytic hp3h s hs).continuousAt
  have hright : AnalyticAt ℂ (fun z =>
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-z))^3)*cubicThetaRegularizedFrequency h z-
        cubicThetaPrimeFirstFactor p z h*cubicThetaRegularizedFrequency (p*h) z) s :=
    ((analyticAt_const.add (analyticAt_const.mul
      ((cubicThetaPrimeNormPower_analytic hp s).pow 3))).mul
      (cubicThetaRegularizedFrequency_analytic hh0 s hs)).sub
    ((cubicThetaPrimeFirstFactor_analytic hp h s).mul
      (cubicThetaRegularizedFrequency_analytic hph s hs))
  exact tendsto_nhds_unique ((hleft.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
    (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

theorem cubicThetaArithmeticFourierResidue_primeHecke {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-(4/3:ℂ)))^3)*
        cubicThetaArithmeticFourierResidue h (4/3)-
      cubicThetaPrimeFirstFactor p (4/3) h*cubicThetaArithmeticFourierResidue (p*h) (4/3) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  have hph : p*h≠0 := mul_ne_zero hp.2.ne_zero hh0
  have hp3h : p^3*h≠0 := mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) hh0
  simpa only [cubicThetaRegularizedFrequency_residue hh0,
    cubicThetaRegularizedFrequency_residue hph,cubicThetaRegularizedFrequency_residue hp3h] using
      cubicThetaRegularizedFrequency_primeHecke hp h hh (s:=(4/3:ℂ)) (by norm_num)

end CubicFirstMoment

end

end OAI
