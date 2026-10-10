import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ReverseGenerators
import OAI.Probability.SLEGauge.ReverseMoments

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
open MeasureTheory
noncomputable section
open Set Filter Real
open scoped Topology
open Set MeasureTheory ProbabilityTheory Topology Function Filter
open scoped NNReal ENNReal ContinuousMapZero
noncomputable section
namespace SLEExactGauge.BrownianRestart
def shift (t : ℝ≥0) (b : Driver) : Driver :=
  ⟨⟨fun s => b (t+s)-b t, (map_continuous b).comp (continuous_const.add continuous_id) |>.sub continuous_const⟩,
    by simp⟩

@[simp] lemma shift_apply (t : ℝ≥0) (b : Driver) (s : ℝ≥0) :
    shift t b s = b (t+s)-b t := rfl

lemma measurable_shift (t : ℝ≥0) : Measurable (shift t) := by
  apply code_embedding.measurable_comp_iff.mp
  exact Measurable.of_eval fun _ =>
    (continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable

lemma indep_shift_history {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (t : ℝ≥0) :
    IndepFun (shift t) (fun b : Driver => fun s : Iic t => b s) W := by
  have hi := (hW.toIsPreBrownianReal.indepFun_shift t).comp
    (Measurable.of_eval (f := fun path : ℝ≥0 → ℝ => fun time : ℚ => path (Real.toNNReal (time:ℝ)))
      (fun _ => measurable_pi_apply _)) measurable_id
  have he : MeasurableSpace.comap (code ∘ shift t) inferInstance =
      MeasurableSpace.comap (shift t) inferInstance := by
    rw [← MeasurableSpace.comap_comp,code_embedding.comap_eq]
  change Indep (MeasurableSpace.comap (code ∘ shift t) inferInstance)
    (MeasurableSpace.comap (fun b : Driver => fun s : Iic t => b s) inferInstance) W at hi
  rw [he] at hi
  exact hi

lemma evaluation_law_unique {W V : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W)
    (hV : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) V) : W = V := by
  let ev : Driver → (ℝ≥0 → ℝ) := fun b => b
  have mev : Measurable ev := Measurable.of_eval fun time => (continuous_eval_const time).measurable
  have hw : IsProjectiveLimit (W.map ev) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict mev]
    exact (hW.hasLaw I).map_eq
  have hv : IsProjectiveLimit (V.map ev) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict mev]
    exact (hV.hasLaw I).map_eq
  have he := hw.unique hv
  have mr : Measurable (fun f : ℝ≥0 → ℝ => fun q : ℚ => f (Real.toNNReal (q:ℝ))) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hc := congrArg (Measure.map (fun f : ℝ≥0 → ℝ => fun q : ℚ => f (Real.toNNReal (q:ℝ)))) he
  rw [Measure.map_map mr mev, Measure.map_map mr mev] at hc
  exact code_embedding.map_injective hc

lemma brownian_shift_map {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (t : ℝ≥0) :
    IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) (W.map (shift t)) where
  hasLaw I := by
    refine ⟨(Measurable.of_eval fun _ => (continuous_eval_const _).measurable).aemeasurable, ?_⟩
    have mm : Measurable (fun b : Driver => I.restrict (fun s => b s)) :=
      Measurable.of_eval fun time => (continuous_eval_const (time:ℝ≥0)).measurable
    rw [Measure.map_map mm (measurable_shift t)]
    exact ((hW.shift t).hasLaw I).map_eq
  cont := Filter.Eventually.of_forall fun b => map_continuous b

lemma shift_preserves_law {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (t : ℝ≥0) :
    W.map (shift t) = W := evaluation_law_unique (brownian_shift_map hW t) hW

end SLEExactGauge.BrownianRestart

namespace SLEExactGauge.BrownianRestart

 
def past (t : ℝ≥0) (b : Driver) : Driver :=
  ⟨⟨fun s => b (min t s), (map_continuous b).comp (continuous_const.min continuous_id)⟩,
    by simp⟩

@[simp] lemma prefix_apply (t : ℝ≥0) (b : Driver) (s : ℝ≥0) :
    past t b s = b (min t s) := rfl

lemma measurable_prefix (t : ℝ≥0) : Measurable (past t) := by
  apply code_embedding.measurable_comp_iff.mp
  exact Measurable.of_eval fun _ => (continuous_eval_const _).measurable

 
def join (t : ℝ≥0) (b c : Driver) : Driver where
  toFun s := if s ≤ t then b s else b t + c (s-t)
  continuous_toFun := by
    apply Continuous.if_le (map_continuous b)
      (continuous_const.add ((map_continuous c).comp (continuous_id.sub continuous_const)))
      continuous_id continuous_const
    intro s hs
    change s = t at hs
    subst s
    simp
  map_zero' := by simp

@[simp] lemma join_apply (t : ℝ≥0) (b c : Driver) (s : ℝ≥0) :
    join t b c s = if s ≤ t then b s else b t + c (s-t) := rfl

lemma measurable_join (t : ℝ≥0) : Measurable (fun q : Driver × Driver => join t q.1 q.2) := by
  apply code_embedding.measurable_comp_iff.mp
  apply Measurable.of_eval
  intro q
  change Measurable (fun v : Driver × Driver => if Real.toNNReal (q:ℝ) ≤ t then
    v.1 (Real.toNNReal (q:ℝ)) else v.1 t + v.2 (Real.toNNReal (q:ℝ)-t))
  split_ifs
  · exact (continuous_eval_const _).measurable.comp measurable_fst
  · exact ((continuous_eval_const _).measurable.comp measurable_fst).add
      ((continuous_eval_const _).measurable.comp measurable_snd)

lemma join_prefix (t : ℝ≥0) (b c : Driver) : join t (past t b) c = join t b c := by
  ext s
  simp only [join_apply,prefix_apply,min_self]
  split_ifs with hs
  · rw [min_eq_right hs]
  · rfl

lemma join_reconstruct (t : ℝ≥0) (b : Driver) : join t (past t b) (shift t b) = b := by
  rw [join_prefix]
  ext s
  simp only [join_apply,shift_apply]
  split_ifs with hs
  · rfl
  · rw [add_tsub_cancel_of_le (le_of_not_ge hs)]
    ring

lemma indep_shift_prefix {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (t : ℝ≥0) :
    IndepFun (shift t) (past t) W := by
  have hi := (indep_shift_history hW t).comp measurable_id
    (Measurable.of_eval (f := fun path : Iic t → ℝ =>
      fun time : ℚ => path ⟨min t (Real.toNNReal (time:ℝ)),by simpa only [Set.mem_Iic] using (min_le_left t (Real.toNNReal (time:ℝ)))⟩)
        (fun q : ℚ => measurable_pi_apply (⟨min t (Real.toNNReal (q:ℝ)),by simpa only [Set.mem_Iic] using (min_le_left t (Real.toNNReal (q:ℝ)))⟩ : Iic t)))
  have he : MeasurableSpace.comap (code ∘ past t) inferInstance =
      MeasurableSpace.comap (past t) inferInstance := by
    rw [← MeasurableSpace.comap_comp,code_embedding.comap_eq]
  change Indep (MeasurableSpace.comap (shift t) inferInstance)
    (MeasurableSpace.comap (code ∘ past t) inferInstance) W at hi
  rw [he] at hi
  exact hi

 

lemma split_map {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (t : ℝ≥0) :
    W.map (fun b => (past t b,shift t b)) = (W.map (past t)).prod W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  rw [(indep_shift_prefix hW t).symm.map_prod_eq_prod_map_map
    (measurable_prefix t).aemeasurable (measurable_shift t).aemeasurable,
    shift_preserves_law hW t]

lemma lintegral_split {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (t : ℝ≥0)
    {F : Driver × Driver → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ b, F (past t b, shift t b) ∂W) =
      ∫⁻ b, ∫⁻ c, F (past t b,c) ∂W ∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  rw [← lintegral_map hF ((measurable_prefix t).prodMk (measurable_shift t)),split_map hW t]
  rw [lintegral_prod _ hF.aemeasurable]
  rw [lintegral_map hF.lintegral_prod_right' (measurable_prefix t)]

 

theorem conditional_join_kernel {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (t : ℝ≥0)
    {F H : Driver → ℝ≥0∞} (hF : Measurable F) (hH : Measurable H) :
    (∫⁻ b, H (past t b) * F b ∂W) =
      ∫⁻ b, H (past t b) * (∫⁻ c, F (join t b c) ∂W) ∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hm := (hH.comp measurable_fst).mul (hF.comp (measurable_join t))
  have he := lintegral_split hW t hm
  change (∫⁻ b, H (past t b) * F (join t (past t b) (shift t b)) ∂W) =
    ∫⁻ b, ∫⁻ c, H (past t b) * F (join t (past t b) c) ∂W ∂W at he
  simp only [join_reconstruct] at he
  simp only [join_prefix] at he
  rw [he]
  apply lintegral_congr
  intro b
  exact lintegral_const_mul _ ((hF.comp (measurable_join t)).comp
    (measurable_const.prodMk measurable_id))

end SLEExactGauge.BrownianRestart

namespace SLEExactGauge.BrownianRestart

 

def reverse (T : ℝ≥0) (b : Driver) : Driver :=
  ⟨⟨fun s => b (max T s) - b (T-s),
    ((map_continuous b).comp (continuous_const.max continuous_id)).sub
      ((map_continuous b).comp (continuous_const.sub continuous_id))⟩, by simp⟩

@[simp] lemma reverse_apply (T : ℝ≥0) (b : Driver) (s : ℝ≥0) :
    reverse T b s = b (max T s)-b (T-s) := rfl

lemma measurable_reverse (T : ℝ≥0) : Measurable (reverse T) := by
  apply code_embedding.measurable_comp_iff.mp
  exact Measurable.of_eval fun _ =>
    (continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable

lemma reverse_brownian {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (T : ℝ≥0) :
    IsBrownianReal (fun s b => reverse T b s) W := by
  have hB := hW.toIsPreBrownianReal
  have hG : IsGaussianProcess (fun s b => reverse T b s) W := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    intro s
    exact ⟨{max T s,T-s},
      { toFun x := x ⟨max T s,by simp⟩ - x ⟨T-s,by simp⟩
        map_add' x y := by simp; abel
        map_smul' c x := by simp; ring },by simp⟩
  refine ⟨hG.isPreBrownianReal_of_covariance ?_ ?_,?_⟩
  · intro t
    simp only [reverse_apply]
    rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
      hB.integral_eval,hB.integral_eval,sub_self]
  · intro s t hst
    let := hG.isProbabilityMeasure
    simp only [reverse_apply]
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right]
    any_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    any_goals exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
    simp only [hB.covariance_fun_eval]
    rw [min_eq_left (max_le_max_left T hst),
      min_eq_right ((tsub_le_self).trans (le_max_left T s)),
      min_eq_left ((tsub_le_self).trans (le_max_left T t)),
      min_eq_right (tsub_le_tsub_left hst T)]
    by_cases hs : s ≤ T
    · rw [max_eq_left hs,NNReal.coe_sub hs]
      ring
    · rw [max_eq_right (le_of_not_ge hs),tsub_eq_zero_of_le (le_of_not_ge hs)]
      simp
  · exact Filter.Eventually.of_forall fun b => map_continuous (reverse T b)

lemma reverse_preserves_law {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (T : ℝ≥0) :
    W.map (reverse T) = W := by
  apply evaluation_law_unique _ hW
  refine ⟨⟨?_⟩, Filter.Eventually.of_forall fun b => map_continuous b⟩
  intro I
  refine ⟨(Measurable.of_eval fun _ => (continuous_eval_const _).measurable).aemeasurable,?_⟩
  have mm : Measurable (fun b : Driver => I.restrict (fun s => b s)) :=
    Measurable.of_eval fun time => (continuous_eval_const (time:ℝ≥0)).measurable
  rw [Measure.map_map mm (measurable_reverse T)]
  exact ((reverse_brownian hW T).hasLaw I).map_eq

lemma reverse_before (T s : ℝ≥0) (hs : s ≤ T) (b : Driver) :
    reverse T b s = b T - b (T-s) := by simp [max_eq_left hs]

lemma reverse_after (T s : ℝ≥0) (hs : T ≤ s) (b : Driver) :
    reverse T b s = b s := by simp [max_eq_right hs,tsub_eq_zero_of_le hs]

end SLEExactGauge.BrownianRestart

namespace SLEExactGauge.BrownianRestart

def backward (T : ℝ≥0) (b : Driver) : Driver := -reverse T b

@[simp] lemma backward_apply (T : ℝ≥0) (b : Driver) (s : ℝ≥0) :
    backward T b s = -(b (max T s)-b (T-s)) := rfl

lemma measurable_backward (T : ℝ≥0) : Measurable (backward T) := by
  apply code_embedding.measurable_comp_iff.mp
  exact Measurable.of_eval fun _ =>
    ((continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable).neg

lemma backward_preserves_law {W : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W) (T : ℝ≥0) :
    W.map (backward T) = W := by
  apply evaluation_law_unique _ hW
  refine ⟨⟨?_⟩, Filter.Eventually.of_forall fun b => map_continuous b⟩
  intro I
  refine ⟨(Measurable.of_eval fun _ => (continuous_eval_const _).measurable).aemeasurable,?_⟩
  have mm : Measurable (fun b : Driver => I.restrict (fun s => b s)) :=
    Measurable.of_eval fun time => (continuous_eval_const (time:ℝ≥0)).measurable
  rw [Measure.map_map mm (measurable_backward T)]
  exact ((reverse_brownian hW T).neg.hasLaw I).map_eq

lemma backward_before {T s : ℝ} (hs : s ∈ Icc 0 T) (b : Driver) :
    backward T.toNNReal b s.toNNReal = b (T-s).toNNReal-b T.toNNReal := by
  have hT : 0 ≤ T := hs.1.trans hs.2
  have hst : s.toNNReal ≤ T.toNNReal := Real.toNNReal_mono hs.2
  have hsub : T.toNNReal-s.toNNReal = (T-s).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_sub hst,Real.coe_toNNReal',max_eq_left hT,max_eq_left hs.1,
      max_eq_left (sub_nonneg.mpr hs.2)]
  simp only [backward_apply,max_eq_left hst,hsub]
  ring
end SLEExactGauge.BrownianRestart

namespace SLEExactGauge.LiteralTrace
open ReverseDerivative

def reversedState (κ y T : ℝ) (b : Driver) : ℝ → ReverseDerivative.State :=
  ReverseDerivative.reverseFlow (a κ) (y/4) (T+y^2) y
    (BrownianRestart.backward T.toNNReal b)

def reversedCurve (κ y T : ℝ) (b : Driver) (s : ℝ) : ℂ :=
  (reversedState κ y T b s).2.1

lemma reverse_reparam_solution {κ y T : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hT : 0 ≤ T)
    (b : Driver) : PositiveSolution κ b
      (reversedCurve κ y T b T+driverValue b T) T
      (fun t => reversedCurve κ y T b (T-t)+driverValue b T) := by
  let β := BrownianRestart.backward T.toNNReal b
  let g := reversedState κ y T b
  let G := reversedCurve κ y T b
  have hq : 0 < y/4 := by positivity
  have ha : 0 ≤ a κ := (div_pos (by norm_num) hκ).le
  have hg := ReverseDerivative.reverseFlow_solution hq (a κ) (T+y^2) y β β.continuous hT
  have hga := ReverseDerivative.reverseFlow_actual hq ha (by linarith : y/4 ≤ y)
    (T+y^2) β β.continuous hT
  have hgc : ContinuousOn G (Icc 0 T) := fun t ht => (hg.2 t ht).continuousWithinAt.snd.fst
  have hheight (t : ℝ) (ht : t ∈ Icc 0 T) : y ≤ (G t).im :=
    ReverseDerivative.reverseFlow_height hq ha hy.le (T+y^2) β β.continuous hT t ht
  have hrev (t : ℝ) (ht : t ∈ Icc 0 T) : T-t ∈ Icc 0 T := by constructor <;> linarith [ht.1,ht.2]
  refine ⟨hT,(hgc.comp (continuous_const.sub continuous_id).continuousOn hrev).add continuousOn_const,?_,?_,?_⟩
  · simp
  · intro t ht
    simpa using hy.trans_le (hheight (T-t) (hrev t ht))
  · intro t ht
    let projG : ReverseDerivative.State →L[ℝ] ℂ :=
      (ContinuousLinearMap.fst ℝ ℂ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℝ))
    have hd := projG.hasFDerivAt.comp_hasDerivWithinAt (T-t) (hga (T-t) (hrev t ht))
    change HasDerivWithinAt G (-(a κ:ℂ)/(G (T-t)-β (T-t).toNNReal)) (Icc 0 T) (T-t) at hd
    have hβ : β (T-t).toNNReal = driverValue b t-driverValue b T := by
      have hh := BrownianRestart.backward_before (hrev t ht) b
      simpa only [sub_sub_cancel,driverValue] using hh
    have hden : G (T-t)-(β (T-t).toNNReal:ℂ) =
        G (T-t)+(driverValue b T:ℂ)-driverValue b t := by rw [hβ,Complex.ofReal_sub]; ring
    rw [hden] at hd
    have hh := (hd.scomp t (((hasDerivAt_const t T).sub (hasDerivAt_id t)).hasDerivWithinAt) hrev).add_const
      (driverValue b T:ℂ)
    convert! hh using 1; first | rfl | (simp only [one_smul,zero_sub,neg_smul,neg_div,neg_neg]; rfl)

lemma inverseFlow_eq_reversedCurve {κ y T : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hT : 0 ≤ T)
    (b : Driver) : inverseFlow κ b T (driverValue b T+y*Complex.I) =
      reversedCurve κ y T b T+driverValue b T := by
  have hf := reverse_reparam_solution hκ hy hT b
  have he := hf.flow_eq
  have hq : 0 < y/4 := by positivity
  have hg := ReverseDerivative.reverseFlow_solution hq (a κ) (T+y^2) y
    (BrownianRestart.backward T.toNNReal b) (BrownianRestart.backward T.toNNReal b).continuous hT
  have hG0 : reversedCurve κ y T b 0 = (y:ℂ)*Complex.I := by
    change (ReverseDerivative.reverseFlow (a κ) (y/4) (T+y^2) y _ 0).2.1 = _
    rw [hg.1]
    apply Complex.ext <;> simp [ReverseDerivative.initial]
  rw [sub_self,hG0] at he
  have he' : flow κ b (reversedCurve κ y T b T+driverValue b T) T =
      driverValue b T+y*Complex.I := he.trans (add_comm _ _)
  rw [← he',inverseFlow_flow hT hf.surviving]
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.ReverseDerivative
open MeasureTheory BrownianCalculus

lemma reverseFlow_log_integral {a q y T : ℝ} (hq : 0 < q) (ha : 0 ≤ a)
    (hy : q ≤ y) (hT : 0 ≤ T) (U : ℝ) (b : Driver) :
    (reverseFlow a q U y b T).2.2 =
      ∫ s in (0:ℝ)..T, a*((((reverseFlow a q U y b s).2.1-(b s.toNNReal:ℂ))⁻¹)^2).re := by
  let g := reverseFlow a q U y b
  have hg := reverseFlow_solution hq a U y b b.continuous hT
  have hd := reverseFlow_actual hq ha hy U b b.continuous hT
  have hc : ContinuousOn g (Icc 0 T) := fun t ht => (hg.2 t ht).continuousWithinAt
  have hz (t : ℝ) (ht : t ∈ Icc 0 T) : (g t).2.1-(b t.toNNReal:ℂ) ≠ 0 := by
    have hh := reverseFlow_height hq ha (hq.le.trans hy) U b b.continuous hT t ht
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    change (reverseFlow a q U y b t).2.1.im = 0 at hi
    linarith
  have hm : ContinuousOn (fun t => (g t).2.1-(b t.toNNReal:ℂ)) (Icc 0 T) :=
    hc.snd.fst.sub ((Complex.continuous_ofReal.comp (b.continuous.comp continuous_real_toNNReal)).continuousOn)
  have hr : ContinuousOn (fun t => a*((((g t).2.1-(b t.toNNReal:ℂ))⁻¹)^2).re) (Icc 0 T) := by
    exact continuousOn_const.mul (Complex.continuous_re.comp_continuousOn ((hm.inv₀ hz).pow 2))
  let projL : State →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℝ))
  have hL (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivWithinAt (fun t => (g t).2.2)
      (a*((((g s).2.1-(b s.toNNReal:ℂ))⁻¹)^2).re) (Icc 0 T) s :=
    projL.hasFDerivAt.comp_hasDerivWithinAt s (hd s hs)
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hc.snd.snd
    (fun s hs => ((hL s ⟨hs.1.le,hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)).hasDerivWithinAt)
    (hr.intervalIntegrable_of_Icc hT)
  change (∫ s in (0:ℝ)..T, a*((((g s).2.1-(b s.toNNReal:ℂ))⁻¹)^2).re) =
    (reverseFlow a q U y b T).2.2-(reverseFlow a q U y b 0).2.2 at he
  rw [hg.1] at he
  simpa only [initial,sub_zero] using he.symm
end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.LiteralTrace
open ReverseDerivative

def reverseCoeff (κ y T : ℝ) (b : Driver) (s : ℝ) : ℂ :=
  (a κ:ℂ)*((reversedCurve κ y T b s-
    (BrownianRestart.backward T.toNNReal b s.toNNReal:ℂ))⁻¹)^2

lemma continuousOn_reverseCoeff {κ y T : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hT : 0 ≤ T)
    (b : Driver) : ContinuousOn (reverseCoeff κ y T b) (Icc 0 T) := by
  let β := BrownianRestart.backward T.toNNReal b
  have hq : 0 < y/4 := by positivity
  have ha : 0 ≤ a κ := (div_pos (by norm_num) hκ).le
  have hg := ReverseDerivative.reverseFlow_solution hq (a κ) (T+y^2) y β β.continuous hT
  have hc : ContinuousOn (reversedCurve κ y T b) (Icc 0 T) := fun t ht => (hg.2 t ht).continuousWithinAt.snd.fst
  have hz (t : ℝ) (ht : t ∈ Icc 0 T) : reversedCurve κ y T b t-(β t.toNNReal:ℂ) ≠ 0 := by
    have hh := ReverseDerivative.reverseFlow_height hq ha hy.le (T+y^2) β β.continuous hT t ht
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    change (ReverseDerivative.reverseFlow (a κ) (y/4) (T+y^2) y β t).2.1.im = 0 at hi
    linarith
  exact continuousOn_const.mul
    (((hc.sub ((Complex.continuous_ofReal.comp (β.continuous.comp continuous_real_toNNReal)).continuousOn)).inv₀ hz).pow 2)

lemma reversed_log_eq_integral {κ y T : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hT : 0 ≤ T)
    (b : Driver) : (reversedState κ y T b T).2.2 =
      (∫ s in (0:ℝ)..T, reverseCoeff κ y T b s).re := by
  have hq : 0 < y/4 := by positivity
  have hh := ReverseDerivative.reverseFlow_log_integral hq
    (by exact (div_pos (by norm_num) hκ).le : 0 ≤ a κ) (by linarith : y/4 ≤ y)
    hT (T+y^2) (BrownianRestart.backward T.toNNReal b)
  change (reversedState κ y T b T).2.2 = Complex.reCLM (∫ s in (0:ℝ)..T, reverseCoeff κ y T b s)
  rw [← Complex.reCLM.intervalIntegral_comp_comm ((continuousOn_reverseCoeff hκ hy hT b).intervalIntegrable_of_Icc hT)]
  simpa only [Complex.reCLM_apply,reverseCoeff,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    reversedState,reversedCurve] using hh
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace
open ReverseDerivative

end SLEExactGauge.LiteralTrace
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
