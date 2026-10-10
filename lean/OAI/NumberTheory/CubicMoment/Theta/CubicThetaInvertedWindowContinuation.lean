import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedWindow

namespace OAI

/-! The computed inverted cusp mean continues as the bounded global
window observation. Its residue is the observation of the inverted residue. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaInvertedWindow_continued {s : ℂ} (hs : 1<s.re) :
    cubicThetaInvertedWindowObservable =ᶠ[𝓝[≠] s]
      (fun z => cubicThetaInvertedScatteringFactor z*
        cubicThetaCuspFourierObservable 0 (cubicThetaHighWindowWeight (4/3)) z) := by
  have hL : MeromorphicOn cubicThetaInvertedWindowObservable {z : ℂ | 1<z.re} :=
    fun _ hz => cubicThetaInvertedWindowObservable_meromorphic hz
  have hR : MeromorphicOn (fun z => cubicThetaInvertedScatteringFactor z*
      cubicThetaCuspFourierObservable 0 (cubicThetaHighWindowWeight (4/3)) z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (cubicThetaInvertedScatteringFactor_analytic z).meromorphicAt.mul
      (cubicThetaCuspFourierObservable_meromorphic _ _ hz)
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaInvertedWindowObservable_normalized hz,
    cubicThetaCuspZeroObservable_normalized _ hz,cubicThetaInvertedConstantContinuation_factor]
  ring

theorem cubicThetaInvertedWindowObservable_residue :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaInvertedWindowObservable s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (inner ℂ (cubicThetaHighWindowL2 (4/3))
        (cubicThetaGlobalInclusion
          (cubicThetaInversionEnergy (cubicThetaArithmeticResidueEnergy (4/3)))))) := by
  let T := (cubicThetaCompactSection_memLp cubicThetaInvertedWindowTest
    cubicThetaInvertedWindowTest.property.2).toLp (cubicThetaSectionRepresentative cubicThetaInvertedWindowTest)
  have h := ((innerSL ℂ T).continuous.tendsto _).comp
    (cubicThetaForcedResolvent_residue (σ:=(4/3:ℝ)) (by norm_num) (by norm_num))
  have he : inner ℂ T (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))=
      inner ℂ (cubicThetaHighWindowL2 (4/3))
        (cubicThetaGlobalInclusion
          (cubicThetaInversionEnergy (cubicThetaArithmeticResidueEnergy (4/3)))) := by
    change inner ℂ (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest
      (cubicThetaInversionSmooth (cubicThetaHighWindowTest (4/3)))))
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))=_
    rw [←cubicThetaInversionEnergy_test]
    exact cubicThetaInversionEnergy_mass_flip
      (cubicThetaGlobalEnergyTest (cubicThetaHighWindowTest (4/3))) _
  change Tendsto (fun s : ℂ => inner ℂ T ((s-((4/3:ℝ):ℂ)) • cubicThetaForcedResolvent s))
    (𝓝[≠] ((4/3:ℝ):ℂ)) (𝓝 (inner ℂ T
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))))) at h
  rw [he] at h
  simpa only [inner_smul_right,Complex.ofReal_div,Complex.ofReal_ofNat,
    cubicThetaInvertedWindowObservable,cubicThetaArithmeticDistribution,T] using h

theorem cubicThetaResidue_inverted_window_pairing :
    inner ℂ (cubicThetaHighWindowL2 (4/3))
      (cubicThetaGlobalInclusion
        (cubicThetaInversionEnergy (cubicThetaArithmeticResidueEnergy (4/3))))=
    inner ℂ (cubicThetaHighWindowL2 (4/3))
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))) := by
  have hO := cubicThetaCuspObservable_residue
    (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight (4/3)))
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hO
  have hF := (cubicThetaInvertedScatteringFactor_analytic (4/3:ℂ)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ))
  have ht := hF.mul hO
  simp only [cubicThetaInvertedScatteringFactor_pole,one_mul] at ht
  have hlim : Tendsto (fun s : ℂ => (s-4/3)*cubicThetaInvertedWindowObservable s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight (4/3)))
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3))))) := by
    apply ht.congr'
    filter_upwards [cubicThetaInvertedWindow_continued (s:=(4/3:ℂ)) (by norm_num)] with s hs
    change cubicThetaInvertedScatteringFactor s*
      ((s-4/3)*cubicThetaCuspFourierObservable 0 (cubicThetaHighWindowWeight (4/3)) s)=_
    rw [hs]
    ring
  exact (tendsto_nhds_unique cubicThetaInvertedWindowObservable_residue hlim).trans
    (cubicThetaHighWindowPairing_energy _ _).symm

end CubicFirstMoment

end

end OAI
