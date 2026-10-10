import Mathlib
import OAI.Probability.SKSupport.Parabolic.ForwardRegularity
import OAI.Probability.SKSupport.Parabolic.TiltedEvolution

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma varianceTilted_time_continuous {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c x : ℝ) :
    Continuous (fun t => varianceTilted c t f g x) := by
  have hNc : Continuous (fun y => g y*Real.exp (c*f y)) :=
    hg.smooth.continuous.mul (Real.continuous_exp.comp (continuous_const.mul hf.smooth.continuous))
  have hNb : ExponentialBound (fun y => g y*Real.exp (c*f y)) := by
    simpa only [iteratedDeriv_zero] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 0
  exact (continuous_varianceHeat hNc hNb x).div
    (continuous_varianceHeat (Real.continuous_exp.comp (continuous_const.mul hf.smooth.continuous))
      (exponentialBound_exp hLip c) x)
    (fun t => ne_of_gt (varianceHeat_exp_pos hLip c t x))

lemma varianceTilted_joint_continuous {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ × ℝ => varianceTilted c p.1 f g p.2) := by
  obtain ⟨L,hL⟩ := varianceTilted_space_lipschitz hf hLip hg hc
  apply continuous_iff_continuousAt.mpr
  intro p
  have hlim : Tendsto (fun q : ℝ × ℝ => (L:ℝ)*|q.2-p.2|+
      |varianceTilted c q.1 f g p.2-varianceTilted c p.1 f g p.2|) (𝓝 p) (𝓝 0) := by
    have hh : Continuous (fun q : ℝ × ℝ => (L:ℝ)*|q.2-p.2|+
        |varianceTilted c q.1 f g p.2-varianceTilted c p.1 f g p.2|) := by
      exact (continuous_const.mul (continuous_snd.sub continuous_const).abs).add
        (((varianceTilted_time_continuous hf hLip hg c p.2).comp continuous_fst).sub continuous_const).abs
    simpa only [sub_self,abs_zero,mul_zero,add_zero] using hh.continuousAt.tendsto (x := p)
  change Tendsto (fun q : ℝ × ℝ => varianceTilted c q.1 f g q.2) (𝓝 p)
    (𝓝 (varianceTilted c p.1 f g p.2))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with q hq
  have hb := (hL q.1).dist_le_mul q.2 p.2
  have htri := dist_triangle (varianceTilted c q.1 f g q.2) (varianceTilted c q.1 f g p.2)
    (varianceTilted c p.1 f g p.2)
  simp only [Real.dist_eq] at hb htri ⊢
  exact (htri.trans (add_le_add hb le_rfl)).trans_lt hq

def tiltedRate (c : ℝ) (f g : ℝ → ℝ) (t x : ℝ) :=
  (1/2:ℝ)*deriv (deriv (varianceTilted c t f g)) x+
    c*deriv (varianceLogHeat c t f) x*deriv (varianceTilted c t f g) x

lemma tiltedRate_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) :
    BoundedSmoothFamily (tiltedRate c f g) := by
  have hU := varianceTilted_family hf hLip hg hc
  exact (hU.deriv.deriv.const_mul (1/2:ℝ)).add (((varianceGradient_family hf hLip hc).const_mul c).mul hU.deriv)

lemma tiltedRate_continuousOn {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => tiltedRate c f g p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  have hU := varianceTilted_family hf hLip hg hc
  have hUc := varianceTilted_joint_continuous hf hLip hg hc
  have hUx := hU.continuous_iteratedDeriv hUc 1
  have hUxx := hU.continuous_iteratedDeriv hUc 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hUx hUxx
  exact (continuous_const.mul hUxx).continuousOn.add
    ((continuousOn_const.mul (varianceGradient_continuousOn hf hLip hc T)).mul hUx.continuousOn)

def tiltedBackward (c T : ℝ) (f g : ℝ → ℝ) (t x : ℝ) := varianceTilted c (T-t) f g x

def tiltedBackwardRate (c T : ℝ) (f g : ℝ → ℝ) (t x : ℝ) := -tiltedRate c f g (T-t) x

lemma tiltedBackward_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    BoundedSmoothFamily (tiltedBackward c T f g) := by
  unfold tiltedBackward
  simpa only [one_mul] using (varianceTilted_family hf hLip hg hc).reparam
    (A := fun t => T-t) (C := fun _ => 1) (measurable_const.sub measurable_id) measurable_const (fun _ => by norm_num)

lemma tiltedBackwardRate_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    BoundedSmoothFamily (tiltedBackwardRate c T f g) := by
  unfold tiltedBackwardRate
  simpa only [one_mul,neg_one_mul] using ((tiltedRate_family hf hLip hg hc).reparam
    (A := fun t => T-t) (C := fun _ => 1) (measurable_const.sub measurable_id) measurable_const
    (fun _ => by norm_num)).const_mul (-1)

lemma tiltedBackward_continuous {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    Continuous (fun p : ℝ × ℝ => tiltedBackward c T f g p.1 p.2) :=
  (varianceTilted_joint_continuous hf hLip hg hc).comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)

lemma tiltedBackwardRate_continuousOn {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => tiltedBackwardRate c T f g p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  change ContinuousOn (fun p : ℝ × ℝ => -tiltedRate c f g (T-p.1) p.2) _
  exact (tiltedRate_continuousOn hf hLip hg hc T |>.neg).comp
    (f := fun p : ℝ × ℝ => (T-p.1,p.2))
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
    (fun p hp => ⟨⟨sub_nonneg.mpr hp.1.2,sub_le_self _ hp.1.1⟩,mem_univ _⟩)

lemma tiltedBackward_time {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c)
    {T t : ℝ} (ht : t < T) (x : ℝ) :
    HasDerivAt (fun u => tiltedBackward c T f g u x) (tiltedBackwardRate c T f g t x) t := by
  have hh := ((varianceTilted_equation hf hLip hg hc (sub_nonneg.mpr ht.le) x).hasDerivAt
    (Ici_mem_nhds (sub_pos.mpr ht))).comp t ((hasDerivAt_id t).const_sub T)
  convert hh using 1 <;> first | rfl | (dsimp [tiltedBackwardRate,tiltedRate];ring)

lemma tiltedBackward_integrated_rate {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c)
    {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
    tiltedBackward c T f g b x-tiltedBackward c T f g a x =
      ∫ t in a..b, tiltedBackwardRate c T f g t x := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact ((tiltedBackward_continuous hf hLip hg hc T).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro t ht
    exact tiltedBackward_time hf hLip hg hc (ht.2.trans_le hb) x
  · apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (tiltedBackwardRate_continuousOn hf hLip hg hc T).comp
      (f := fun t : ℝ => (t,x)) (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨⟨ha.trans ht.1,ht.2.trans hb⟩,mem_univ _⟩)

lemma tiltedBackward_terminal (c T : ℝ) (f g : ℝ → ℝ) (x : ℝ) : tiltedBackward c T f g T x=g x := by
  simp only [tiltedBackward,sub_self,varianceTilted,varianceHeat_zero]
  exact mul_div_cancel_right₀ _ (Real.exp_ne_zero _)

end ZeroTemperatureSK.Heat

end
end

end OAI
