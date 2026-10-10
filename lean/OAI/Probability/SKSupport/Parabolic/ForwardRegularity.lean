import Mathlib
import OAI.Probability.SKSupport.Regularity.GaussianFlowRegularity
import OAI.Probability.SKSupport.Moments.FamilyReparam
import OAI.Probability.SKSupport.Parabolic.ForwardGeometry
import OAI.Probability.SKSupport.Regularity.GaussianValueContinuity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma forwardCorrection_smooth {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t : ℝ) :
    ContDiff ℝ ∞ (forwardCorrection a f t) := by
  exact contDiff_const.add ((regularDatum_varianceLogHeat hf hLip (by norm_num : (0:ℝ)≤1) _).smooth.comp
    (contDiff_const.mul contDiff_id))

lemma forwardCorrection_deriv {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t x : ℝ) :
    deriv (forwardCorrection a f t) x = forwardScale a t*
      deriv (varianceLogHeat 1 (forwardVariance a t) f) (forwardScale a t*x) := by
  have hs := ((regularDatum_varianceLogHeat hf hLip (by norm_num : (0:ℝ)≤1) (forwardVariance a t)).smooth.differentiable
    (by simp) (forwardScale a t*x)).hasDerivAt
  have hd := (hs.comp x ((hasDerivAt_id x).const_mul (forwardScale a t))).const_add
    ((1/2:ℝ)*Real.log (forwardScale a t))
  convert hd.deriv using 1 <;> first | rfl | ring

lemma forwardGradient_family {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    BoundedSmoothFamily (fun t => deriv (forwardCorrection a f t)) := by
  have hb (t) : |forwardScale a t| ≤ (1:ℝ≥0) := by
    rw [abs_of_pos (forwardScale_pos ha t)]
    exact forwardScale_le_one ha t
  have hh := ((varianceGradient_family hf hLip (by norm_num : (0:ℝ)≤1)).reparam
    (continuous_forwardVariance ha).measurable (continuous_forwardScale ha).measurable hb).timeMul
    (continuous_forwardScale ha).measurable hb
  convert hh using 1
  funext t x
  exact forwardCorrection_deriv hf hLip t x

lemma forwardCorrection_regular {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t : ℝ) :
    RegularDatum (forwardCorrection a f t) :=
  ⟨forwardCorrection_smooth hf hLip t,(forwardGradient_family ha hf hLip).regular t⟩

lemma forwardCorrection_jet {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (n : ℕ) (t x : ℝ) :
    iteratedDeriv (n+1) (forwardCorrection a f t) x = (forwardScale a t)^(n+1)*
      iteratedDeriv (n+1) (varianceLogHeat 1 (forwardVariance a t) f) (forwardScale a t*x) := by
  have hg := (regularDatum_varianceLogHeat hf hLip (by norm_num : (0:ℝ)≤1) (forwardVariance a t)).deriv_bounded.smooth
  have he : deriv (forwardCorrection a f t) = fun x => forwardScale a t*
      deriv (varianceLogHeat 1 (forwardVariance a t) f) (forwardScale a t*x) :=
    funext (forwardCorrection_deriv hf hLip t)
  rw [iteratedDeriv_succ',he,iteratedDeriv_const_mul_field,scaled_composition_jet hg]
  rw [← iteratedDeriv_succ']
  ring

lemma forwardCorrection_continuous {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    Continuous (fun p : ℝ × ℝ => forwardCorrection a f p.1 p.2) := by
  exact (continuous_const.mul (((continuous_forwardScale ha).comp continuous_fst).log
    (fun p => ne_of_gt (forwardScale_pos ha p.1)))).add
    ((varianceLogHeat_joint_continuous hf hLip (by norm_num : (0:ℝ)≤1)).comp
      (((continuous_forwardVariance ha).comp continuous_fst).prodMk
        (((continuous_forwardScale ha).comp continuous_fst).mul continuous_snd)))

lemma forwardGradient_continuous {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    Continuous (fun p : ℝ × ℝ => deriv (forwardCorrection a f p.1) p.2) := by
  obtain ⟨C,hC⟩ := (forwardGradient_family ha hf hLip).deriv.bound
  have hh := continuousOn_deriv_family
    (S := Set.univ) (forwardCorrection_continuous ha hf hLip).continuousOn
    (fun t _ => (forwardCorrection_smooth hf hLip t).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) C.coe_nonneg (fun t _ x => hC t x)
  exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using hh)

lemma forwardCorrection_even {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f) (t : ℝ) :
    Function.Even (forwardCorrection a f t) := by
  have heq : varianceLogHeat 1 (forwardVariance a t) f =
      logSemigroup 1 (Real.toNNReal (forwardVariance a t)) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hLip.continuous.measurable 1 _)
  have hEven := logSemigroup_even hf.smooth.continuous.measurable he 1 (Real.toNNReal (forwardVariance a t))
  intro x
  simp only [forwardCorrection,heq,mul_neg]
  rw [hEven]

def forwardCorrectionRate (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2:ℝ)*iteratedDeriv 2 (forwardCorrection a f t) x+
    (1/2:ℝ)*(deriv (forwardCorrection a f t) x)^2-
    (x/forwardTime a t)*deriv (forwardCorrection a f t) x-
    (1/2:ℝ)/forwardTime a t

lemma hasDerivAt_forwardCorrection {a t : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => forwardCorrection a f s x) (forwardCorrectionRate a f t x) t := by
  have hh := hasDerivAt_varianceLogHeat_curve hf hLip 1 (hasDerivAt_forwardVariance ha ht)
    ((hasDerivAt_forwardScale ha ht).mul_const x) (forwardVariance_pos ha ht)
  have hl := ((hasDerivAt_forwardScale ha ht).log (ne_of_gt (forwardScale_pos ha t))).const_mul (1/2:ℝ)
  convert hl.add hh using 1 <;> first | rfl | skip
  rw [forwardCorrectionRate,forwardCorrection_jet hf hLip 1,forwardCorrection_deriv hf hLip]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  field_simp [ne_of_gt (forwardTime_pos ha t),ne_of_gt (forwardScale_pos ha t)]
  ring

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def AffineSmoothFamily (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ A B : ℝ → ℝ → ℝ, BoundedSmoothFamily A ∧
    Continuous (fun p : ℝ × ℝ => A p.1 p.2) ∧ BoundedSmoothFamily B ∧
    Continuous (fun p : ℝ × ℝ => B p.1 p.2) ∧ F = fun t x => A t x+x*B t x

lemma BoundedSmoothFamily.continuous_iteratedDeriv {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => _root_.iteratedDeriv n (F p.1) p.2) := by
  exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using
    hF.continuousOn_iteratedDeriv (S := univ) hc.continuousOn n)

lemma BoundedSmoothFamily.affine {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    AffineSmoothFamily F := by
  refine ⟨F,fun _ _ => 0,hF,hc,BoundedSmoothFamily.timeConst (C := 0) measurable_const
    (fun _ => by simp),continuous_const,?_⟩
  funext t x
  simp

lemma BoundedSmoothFamily.affine_id_mul {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    AffineSmoothFamily (fun t x => x*F t x) := by
  refine ⟨fun _ _ => 0,F,BoundedSmoothFamily.timeConst (C := 0) measurable_const
    (fun _ => by simp),continuous_const,hF,hc,?_⟩
  funext t x
  simp

lemma AffineSmoothFamily.add {F G : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (hG : AffineSmoothFamily G) :
    AffineSmoothFamily (fun t x => F t x+G t x) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  obtain ⟨C,D,hC,hCc,hD,hDc,rfl⟩ := hG
  refine ⟨fun t x => A t x+C t x,fun t x => B t x+D t x,hA.add hC,hAc.add hCc,
    hB.add hD,hBc.add hDc,?_⟩
  funext t x
  ring

lemma AffineSmoothFamily.const_mul {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (c : ℝ) : AffineSmoothFamily (fun t x => c*F t x) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  refine ⟨fun t x => c*A t x,fun t x => c*B t x,hA.const_mul c,hAc.const_mul c,
    hB.const_mul c,hBc.const_mul c,?_⟩
  funext t x
  ring

lemma AffineSmoothFamily.continuous {F : ℝ → ℝ → ℝ} (hF : AffineSmoothFamily F) :
    Continuous (fun p : ℝ × ℝ => F p.1 p.2) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  exact hAc.add (continuous_snd.mul hBc)

lemma AffineSmoothFamily.smooth {F : ℝ → ℝ → ℝ} (hF : AffineSmoothFamily F) (t : ℝ) :
    ContDiff ℝ ∞ (F t) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  exact (hA.regular t).smooth.add (contDiff_id.mul (hB.regular t).smooth)

lemma AffineSmoothFamily.deriv {F : ℝ → ℝ → ℝ} (hF : AffineSmoothFamily F) :
    AffineSmoothFamily (fun t => _root_.deriv (F t)) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  have hdA : Continuous (fun p : ℝ × ℝ => _root_.deriv (A p.1) p.2) := by
    simpa only [iteratedDeriv_one] using hA.continuous_iteratedDeriv hAc 1
  have hdB : Continuous (fun p : ℝ × ℝ => _root_.deriv (B p.1) p.2) := by
    simpa only [iteratedDeriv_one] using hB.continuous_iteratedDeriv hBc 1
  refine ⟨fun t x => _root_.deriv (A t) x+B t x,fun t => _root_.deriv (B t),
    hA.deriv.add hB,hdA.add hBc,hB.deriv,hdB,?_⟩
  funext t x
  have hh := ((hA.regular t).smooth.differentiable (by simp) x).hasDerivAt.add
    ((hasDerivAt_id x).mul ((hB.regular t).smooth.differentiable (by simp) x).hasDerivAt)
  convert hh.deriv using 1 <;> first | rfl | (simp only [id_eq];ring)

lemma AffineSmoothFamily.iteratedDeriv {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (n : ℕ) :
    AffineSmoothFamily (fun t => _root_.iteratedDeriv n (F t)) := by
  induction n with
  | zero => exact hF
  | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv

lemma AffineSmoothFamily.bound {F : ℝ → ℝ → ℝ} (hF : AffineSmoothFamily F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, |F t x| ≤ C*(1+|x|) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  obtain ⟨C,hC⟩ := hA.bound
  obtain ⟨D,hD⟩ := hB.bound
  refine ⟨C+D, by positivity,fun t x => ?_⟩
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have hh := mul_le_mul_of_nonneg_left (hD t x) (abs_nonneg x)
  nlinarith [hC t x,mul_nonneg C.coe_nonneg (abs_nonneg x)]

lemma AffineSmoothFamily.intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (x a b : ℝ) :
    IntervalIntegrable (fun t => F t x) volume a b :=
  (hF.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _

lemma AffineSmoothFamily.hasDerivAt_integral {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (a b x : ℝ) :
    HasDerivAt (fun z => ∫ t in a..b, F t z) (∫ t in a..b, _root_.deriv (F t) x) x := by
  obtain ⟨C,hC,hbound⟩ := hF.deriv.bound
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => F t z) (F' := fun z t => _root_.deriv (F t) z)
    (bound := fun _ => C*(2+|x|)) (s := Metric.ball x 1) (Metric.ball_mem_nhds x zero_lt_one)
    (Eventually.of_forall (fun z => (hF.continuous.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable))
    (hF.intervalIntegrable x a b) ((hF.deriv.continuous.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable) ?_
    (intervalIntegrable_const) ?_).2
  · filter_upwards [] with t ht z hz
    have hz' : |z-x| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hz
    have habs : |z| ≤ 1+|x| := by
      have hh := abs_add_le (z-x) x
      rw [sub_add_cancel] at hh
      linarith
    exact (hbound t z).trans (by nlinarith)
  · filter_upwards [] with t ht z hz
    exact ((hF.smooth t).differentiable (by simp) z).hasDerivAt

lemma AffineSmoothFamily.iteratedDeriv_integral {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (n : ℕ) (a b x : ℝ) :
    _root_.iteratedDeriv n (fun z => ∫ t in a..b, F t z) x =
      ∫ t in a..b, _root_.iteratedDeriv n (F t) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n hn =>
    have he : _root_.iteratedDeriv n (fun z => ∫ t in a..b, F t z) =
        fun z => ∫ t in a..b, _root_.iteratedDeriv n (F t) z := funext hn
    rw [iteratedDeriv_succ,he]
    simpa only [iteratedDeriv_succ] using ((hF.iteratedDeriv n).hasDerivAt_integral a b x).deriv

end ZeroTemperatureSK.Heat

end
end

end OAI
