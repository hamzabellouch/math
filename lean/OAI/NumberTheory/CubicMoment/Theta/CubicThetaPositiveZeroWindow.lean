import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveRadialWindow

namespace OAI

/-! The zero Fourier mode at every positive cutoff. The incoming Mellin
term is entire and therefore contributes no residue. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment
local instance cubicThetaPositiveZeroWindowMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaPositiveZeroWindowProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaFullTorus_zero {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2<s.re) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaFullTorus v s)) 0=
      cubicThetaEisensteinConstantMode v s := by
  let L := (cubicThetaTorusCoefficientMap 0).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaFullTorus v s)=_
  rw [cubicThetaFullTorus,map_add,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusCoefficientMap_apply,
    cubicThetaTorusFourier_toLp,cubicThetaTorusCoefficient_basis,ite_true,
    smul_eq_mul,mul_one,cubicThetaArithmeticTorus_zero hv hs,sub_add_cancel]

lemma cubicThetaEisenstein_horizontal_zero {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) :
    (∫ z in cubicThetaHorizontalCell,star (cubicThetaHorizontalCharacter 0 z)*
      cubicThetaEisenstein (z,v) s)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaEisensteinConstantMode v s := by
  unfold cubicThetaHorizontalCharacter
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaEisenstein (z,v) s)
    (cubicThetaFullTorus v s) 0 (cubicThetaFullTorus_real hv hs),
    cubicThetaFullTorus_zero hv hs]
  rfl

lemma cubicThetaPositiveZeroObservable_normalized (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 3<s.re) :
    cubicThetaPositiveFourierObservable 0 W hε hW s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (s-2)+
      ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*mellin (star W) (-s) := by
  rw [cubicThetaPositiveFourierObservable_iterated 0 W hε hW hs]
  calc
    _ = ∫ v in Ioi ε,
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(star (W v)*(v:ℂ)^s/(v:ℂ)^3)+
        ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*
          (star (W v)*(v:ℂ)^(2-s)/(v:ℂ)^3) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaEisenstein_horizontal_zero (hε.trans hv) (by linarith),
        cubicThetaEisensteinConstantMode_eq (hε.trans hv) (by linarith),
        cubicThetaConstantContinuation_right (by linarith)]
      have he := cubicThetaPeriod_fourier_constant
      linear_combination (star (W v)/(v:ℂ)^3/(s-1)*
        cubicThetaConstantContinuation s*(v:ℂ)^(2-s))*he
    _ = ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (s-2)+
        ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*mellin (star W) (-s) := by
      rw [integral_add
        ((cubicThetaPositiveWindow_power_integrable W hε hW s).const_mul _)
        ((cubicThetaPositiveWindow_power_integrable W hε hW (2-s)).const_mul _),
        integral_const_mul,integral_const_mul,
        cubicThetaPositiveWindow_power W hε hW s,
        cubicThetaPositiveWindow_power W hε hW (2-s)]
      congr 3
      ring

theorem cubicThetaPositiveZeroObservable_continued (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 1<s.re) :
    cubicThetaPositiveFourierObservable 0 W hε hW =ᶠ[𝓝[≠] s]
      (fun z => ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (z-2)+
        ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*mellin (star W) (-z)) := by
  have hm := cubicThetaPositiveWindow_entire W hε hW
  have ho : MeromorphicOn (cubicThetaPositiveFourierObservable 0 W hε hW)
      {z : ℂ | 1<z.re} :=
    fun z hz => cubicThetaPositiveFourierObservable_meromorphic 0 W hε hW hz
  have hr : MeromorphicOn (fun z => ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (z-2)+
      ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*mellin (star W) (-z))
      {z : ℂ | 1<z.re} := by
    intro z _
    exact (((hm.comp (differentiable_id.sub_const 2)).const_mul _).analyticAt z).meromorphicAt.add
      ((((MeromorphicAt.const (Real.pi:ℂ) z).div
        (analyticAt_id.sub analyticAt_const).meromorphicAt).mul
          (cubicThetaConstantContinuation_meromorphic z)).mul
            ((hm.comp differentiable_id.neg).analyticAt z).meromorphicAt)
  apply cubicThetaMeromorphic_identity ho hr (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  exact cubicThetaPositiveZeroObservable_normalized W hε hW hz

theorem cubicThetaPositiveResidue_zero_observation (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 0 W hε hW)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))=
      (3*Real.pi:ℂ)*cubicThetaScatteringResidue*mellin (star W) (-(4/3:ℂ)) := by
  have hm := (cubicThetaPositiveWindow_entire W hε hW).continuous
  have hA : ContinuousAt (fun s : ℂ =>
      ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (s-2)) (4/3) :=
    continuousAt_const.mul (hm.continuousAt.comp (continuousAt_id.sub_const 2))
  have hB : ContinuousAt (fun s : ℂ =>
      (Real.pi:ℂ)/(s-1)*mellin (star W) (-s)) (4/3) :=
    (continuousAt_const.div (continuousAt_id.sub_const 1) (by norm_num)).mul
      (hm.continuousAt.comp continuousAt_id.neg)
  have hz : Tendsto (fun s : ℂ => s-4/3) (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    have hc : ContinuousAt (fun s : ℂ => s-4/3) (4/3:ℂ) :=
      continuousAt_id.sub_const _
    simpa only [sub_self] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (hz.mul (hA.tendsto.mono_left nhdsWithin_le_nhds)).add
    ((hB.tendsto.mono_left nhdsWithin_le_nhds).mul cubicThetaConstantContinuation_residue)
  change Tendsto _ _ (𝓝 ((0:ℂ)*
    (((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) ((4/3:ℂ)-2))+
    ((Real.pi:ℂ)/((4/3:ℂ)-1)*mellin (star W) (-(4/3:ℂ)))*
      cubicThetaScatteringResidue)) at ht
  have hl : (0:ℂ)*(((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) ((4/3:ℂ)-2))+
      ((Real.pi:ℂ)/((4/3:ℂ)-1)*mellin (star W) (-(4/3:ℂ)))*cubicThetaScatteringResidue=
      (3*Real.pi:ℂ)*cubicThetaScatteringResidue*mellin (star W) (-(4/3:ℂ)) := by ring
  rw [hl] at ht
  apply tendsto_nhds_unique (cubicThetaPositiveFourierObservable_residue 0 W hε hW)
  apply ht.congr'
  filter_upwards [cubicThetaPositiveZeroObservable_continued W hε hW
    (s:=(4/3:ℂ)) (by norm_num)] with s hs
  rw [hs]
  ring

end CubicFirstMoment

end

end OAI
