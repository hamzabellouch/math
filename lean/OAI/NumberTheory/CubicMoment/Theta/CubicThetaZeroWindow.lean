import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScatteringRegularResidue

namespace OAI

/-! Compact radial windows supported above height two retain the exact
constant-mode continuation. They will test the high annular forcing. -/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaZeroRadialWindow_mellin (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) (s : ℂ) :
    cubicThetaZeroRadialTest W s=
      mellin (star W) (-s) := by
  have he : (∫ v in Ioi (2:ℝ), star (W v)*(v:ℂ)^(2-s)/(v:ℂ)^3)=
      ∫ v in Ioi (2:ℝ), (v:ℂ)^(-s-1)*star (W v) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    change 2<v at hv
    dsimp only
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hp : (v:ℂ)^(2-s)/(v:ℂ)^3=(v:ℂ)^(-s-1) := by
      rw [← Complex.cpow_natCast,← Complex.cpow_sub _ _ hv0]
      congr 1
      norm_num
      ring
    calc
      _ = ((v:ℂ)^(2-s)/(v:ℂ)^3)*star (W v) := by ring
      _ = _ := by rw [hp]
  unfold cubicThetaZeroRadialTest
  rw [he]
  have h₂ : (∫ v in Ioi (2:ℝ), (v:ℂ)^(-s-1)*star (W v))=
      ∫ v : ℝ, (v:ℂ)^(-s-1)*star (W v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hW v (le_of_not_gt hv),star_zero,mul_zero]
  have h₀ : (∫ v in Ioi (0:ℝ), (v:ℂ)^(-s-1)*star (W v))=
      ∫ v : ℝ, (v:ℂ)^(-s-1)*star (W v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hW v (le_trans (le_of_not_gt hv) (by norm_num)),star_zero,mul_zero]
  rw [h₂,← h₀]
  rfl

lemma cubicThetaZeroRadialWindow_entire (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) :
    Differentiable ℂ (cubicThetaZeroRadialTest W) := by
  have hpos : tsupport (star W)⊆Ioi (0:ℝ) := by
    have hs : tsupport (star W)⊆Ici (2:ℝ) := by
      apply closure_minimal ?_ isClosed_Ici
      intro v hv
      by_contra hn
      apply hv
      change star (W v)=0
      rw [hW v (le_of_not_ge hn),star_zero]
    intro v hv
    exact lt_of_lt_of_le (show (0:ℝ)<2 by norm_num) (hs hv)
  have hm := smooth_mellin_entire (star W) (star W).hasCompactSupport
    hpos (star W).continuous
  have he : cubicThetaZeroRadialTest W=(fun s : ℂ => mellin (star W) (-s)) :=
    funext (cubicThetaZeroRadialWindow_mellin W hW)
  rw [he]
  exact hm.comp differentiable_id.neg

theorem cubicThetaCuspZeroWindow_continued (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) {s : ℂ} (hs : 1<s.re) :
    cubicThetaCuspFourierObservable 0 W =ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*
        cubicThetaZeroRadialTest W z) := by
  have ho : MeromorphicOn (cubicThetaCuspFourierObservable 0 W) {z : ℂ | 1<z.re} :=
    fun z hz => cubicThetaCuspFourierObservable_meromorphic 0 W hz
  have hr : MeromorphicOn (fun z => ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*
      cubicThetaZeroRadialTest W z) {z : ℂ | 1<z.re} := by
    intro z _
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (analyticAt_id.sub analyticAt_const).meromorphicAt).mul
        (cubicThetaConstantContinuation_meromorphic z)).mul
          ((cubicThetaZeroRadialWindow_entire W hW).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity ho hr (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  exact cubicThetaCuspZeroObservable_normalized W hz

theorem cubicThetaSpectralResidue_window_zero_closed (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))=0 := by
  have hs1 : (σ:ℂ)-1≠0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  have hc : ContinuousAt (fun s : ℂ => ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*
      cubicThetaZeroRadialTest W s) (σ:ℂ) :=
    ((continuousAt_const.div (continuousAt_id.sub continuousAt_const) hs1).mul
      (cubicThetaConstantContinuation_regular (by simpa using hσ) hne).continuousAt).mul
        ((cubicThetaZeroRadialWindow_entire W hW).continuous.continuousAt (x:=(σ:ℂ)))
  have hs : Tendsto (fun s : ℂ => s-(σ:ℂ)) (𝓝[≠] (σ:ℂ)) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ => s-(σ:ℂ)) (σ:ℂ) :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using h.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaCuspFourierObservable 0 W s)
      (𝓝[≠] (σ:ℂ)) (𝓝 0) := by
    have hprod := hs.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
    simp only [zero_mul] at hprod
    apply hprod.congr'
    filter_upwards [cubicThetaCuspZeroWindow_continued W hW (by simpa using hσ)] with s hs
    rw [hs]
  exact tendsto_nhds_unique (cubicThetaCuspObservable_residue_closed
    (cubicThetaCuspFourierTest 0 W) hσ hσ2) ht

theorem cubicThetaSpectralResidue_window_zero (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))=0 :=
  cubicThetaSpectralResidue_window_zero_closed W hW hσ hσ2.le hne

end CubicFirstMoment

end

end OAI
