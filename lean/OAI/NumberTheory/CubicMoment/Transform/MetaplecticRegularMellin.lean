import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSmoothScale
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticDecompletion
import OAI.NumberTheory.CubicMoment.Estimates.GammaQuotientGrowth
import OAI.NumberTheory.CubicMoment.Estimates.SmoothNormPartition

namespace OAI

/-! A regularized Mellin transform built from the actual Voronoi sum.
The smooth subtraction vanishes near zero and agrees exactly with the
published main term for large scale. No continuation is assumed. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators ContDiff
namespace CubicFirstMoment

def metaplecticRegularScale (r : Eisenstein) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  metaplecticCompleted r 0 W X-
    metaplecticCompletedResidue r*mellin W (5/6)*((X^(5/6:ℝ):ℝ):ℂ)*(normPartitionStep X:ℂ)

lemma metaplecticMain_zero_mode (r : Eisenstein) (W : ℝ → ℂ) (X : ℝ) :
    metaplecticMain r 0 W X =
      metaplecticCompletedResidue r*mellin W (5/6)*((X^(5/6:ℝ):ℝ):ℂ) := by
  simp only [metaplecticMain,ite_true,metaplecticCompletedResidue,Complex.ofReal_mul]
  ring

lemma continuousOn_metaplecticRegularScale (r : Eisenstein) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hc : Continuous W) :
    ContinuousOn (metaplecticRegularScale r W) (Ioi 0) := by
  apply (continuousOn_metaplecticCompleted_scale r 0 W hW hc).sub
  apply Continuous.continuousOn
  have hp : Continuous (fun X : ℝ => ((X^(5/6:ℝ):ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num))
  have hs : Continuous (fun X : ℝ => (normPartitionStep X:ℂ)) := by
    unfold normPartitionStep
    fun_prop
  exact (continuous_const.mul hp).mul hs

lemma metaplecticRegularScale_zero_near_zero (r : Eisenstein) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) :
    metaplecticRegularScale r W =ᶠ[𝓝[>] (0:ℝ)] 0 := by
  obtain ⟨B,hB⟩ := hW.isCompact.isBounded.exists_norm_le
  let B' := max B 1
  have hBp : 0 < B' := zero_lt_one.trans_le (le_max_right _ _)
  have hcut : ∀ x : ℝ, B' < x → W x = 0 := by
    intro x hx
    by_contra hn
    have hh := hB x (subset_tsupport W hn)
    rw [Real.norm_eq_abs] at hh
    have hBB : B ≤ B' := le_max_left _ _
    linarith [le_abs_self x]
  have hη : 0 < min 1 (1/B') := lt_min zero_lt_one (one_div_pos.mpr hBp)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds] with X hX hηX
  have hXp : 0 < X := hX
  have hz := metaplecticCompleted_scale_small r 0 W hBp hcut hXp
    (hηX.trans_le (min_le_right _ _))
  simp only [metaplecticRegularScale,hz,normPartitionStep_zero
    (hηX.trans_le (min_le_left _ _)).le,Complex.ofReal_zero,mul_zero,sub_zero,Pi.zero_apply]

lemma metaplecticRegularScale_decay
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    metaplecticRegularScale r W =O[atTop] (fun X : ℝ => X^(-(1/20000:ℝ))) := by
  have hfamily := uniformLogWeights_constant (ι := Unit) W hW hpos hsm
  have hGamma : AngularGammaQuotientStripBound (metaplecticAngularShift 0)
      (-(1/20000:ℝ)-1/6) := by
    apply angularGammaQuotientStripBound_proved
    norm_num [metaplecticAngularShift]
  obtain ⟨K,hK,hbound⟩ := uniform_metaplectic_completed_low hV hfamily 0
    (ε := 1) (σ := 1/20000) (by norm_num) (by norm_num) (by norm_num) hGamma
  apply IsBigO.of_bound (K*Real.sqrt (norm r)*norm r^(1+2*(1/20000:ℝ)))
  filter_upwards [eventually_ge_atTop (2:ℝ)] with X hX
  have hb := hbound () r hr hsr X (by linarith)
  rw [metaplecticRegularScale,normPartitionStep_one (by linarith),
    Complex.ofReal_one,mul_one,←metaplecticMain_zero_mode]
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ X) _)] using hb

lemma metaplecticRegularMellin_differentiableOn
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    DifferentiableOn ℂ (fun s => mellin (metaplecticRegularScale r W) (-s))
      {s : ℂ | 0 < s.re} := by
  have hc : LocallyIntegrableOn (metaplecticRegularScale r W) (Ioi 0) volume :=
    (continuousOn_metaplecticRegularScale r W hW hsm.continuous).locallyIntegrableOn
      measurableSet_Ioi
  have ht := metaplecticRegularScale_decay hV hr hsr W hW hpos hsm
  have hz := metaplecticRegularScale_zero_near_zero r W hW
  intro s hs
  have hb : metaplecticRegularScale r W =O[𝓝[>] (0:ℝ)]
      (fun X : ℝ => X^(-(-s.re-1))) :=
    (isBigO_zero _ _).congr' hz.symm Filter.EventuallyEq.rfl
  have hd := mellin_differentiableAt_of_isBigO_rpow hc ht
    (s := -s) (by change -s.re < (1/20000:ℝ); change 0 < s.re at hs; linarith)
    hb (by simp)
  exact (hd.comp s differentiableAt_id.neg).differentiableWithinAt

lemma metaplecticRegularMellin_convergent
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (metaplecticRegularScale r W) (-s) := by
  have hc : LocallyIntegrableOn (metaplecticRegularScale r W) (Ioi 0) volume :=
    (continuousOn_metaplecticRegularScale r W hW hsm.continuous).locallyIntegrableOn
      measurableSet_Ioi
  have ht := metaplecticRegularScale_decay hV hr hsr W hW hpos hsm
  have hz := metaplecticRegularScale_zero_near_zero r W hW
  have hb : metaplecticRegularScale r W =O[𝓝[>] (0:ℝ)]
      (fun X : ℝ => X^(-(-s.re-1))) :=
    (isBigO_zero _ _).congr' hz.symm Filter.EventuallyEq.rfl
  exact mellinConvergent_of_isBigO_rpow hc ht
    (by change -s.re < (1/20000:ℝ); linarith) hb (by simp)

end CubicFirstMoment

end

end OAI
