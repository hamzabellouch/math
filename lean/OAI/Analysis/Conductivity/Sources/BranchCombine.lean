import Mathlib
import OAI.Analysis.Conductivity.Sources.CopiedScalarCoefficient

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma source_child_push_inner_zero (v w : H10)
    (hv : SourceSupported v.val) (hw : SourceSupported w.val) :
    inner ℝ (weakGradientL (childZeroTransport 0 v).val)
      (weakGradientL (childZeroTransport 1 w).val)=0 := by
  rw [L2.inner_def]
  apply (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [weakGradientL_apply_ae (childZeroTransport 0 v).val,
    weakGradientL_apply_ae (childZeroTransport 1 w).val,
    childH10Transport_support 0 v hv,childH10Transport_support 1 w hw] with x h0 h1 hs0 hs1
  rw [h0,h1]
  have hd := source_child_closed_disjoint (show (0:Fin 2)≠1 by decide)
  by_cases hx : x∈sourceChildEuclidean (actualChildSign 0) '' closure sourceDomain
  · have hn := Set.disjoint_left.mp hd hx
    have he := congrArg jetGradient (hs1 hn)
    change weakGradient (childZeroTransport 1 w).val x=0 at he
    rw [he,inner_zero_right]
  · have he := congrArg jetGradient (hs0 hx)
    change weakGradient (childZeroTransport 0 v).val x=0 at he
    rw [he,inner_zero_left]

def sourceBranchCombine (α β : ℝ) (v w : H10) : H10 :=
  α • childZeroTransport 0 v+β • childZeroTransport 1 w

lemma sourceBranchCombine_support {v w : H10} (hv : SourceSupported v.val)
    (hw : SourceSupported w.val) (α β : ℝ) :
    SourceSupported (sourceBranchCombine α β v w).val :=
  ((hv.child 0).smul α).add ((hw.child 1).smul β)

private lemma norm_smul_sq_real {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (x : E) : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma sourceBranchCombine_energy (α β : ℝ) (v w : H10)
    (hv : SourceSupported v.val) (hw : SourceSupported w.val) :
    ‖weakGradientL (sourceBranchCombine α β v w).val‖^2=
      sourceScale*(α^2*‖weakGradientL v.val‖^2+β^2*‖weakGradientL w.val‖^2) := by
  have horth : inner ℝ (α • weakGradientL (childZeroTransport 0 v).val)
      (β • weakGradientL (childZeroTransport 1 w).val) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right,
      source_child_push_inner_zero v w hv hw, mul_zero, mul_zero]
  have hnorm := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  simp only [← pow_two] at hnorm
  change ‖weakGradientL (α • (childZeroTransport 0 v).val+β • (childZeroTransport 1 w).val)‖^2=_
  rw [map_add,map_smul,map_smul,hnorm]
  rw [norm_smul_sq_real, norm_smul_sq_real]
  change α^2*‖weakGradientL (childH10Transport 0 v)‖^2+β^2*‖weakGradientL (childH10Transport 1 w)‖^2=_
  calc
    _ = α^2*(sourceScale*‖weakGradientL v.val‖^2)+β^2*(sourceScale*‖weakGradientL w.val‖^2) :=
      congrArg₂ (fun r t : ℝ => α^2*r+β^2*t) (child_gradient_norm_sq 0 v) (child_gradient_norm_sq 1 w)
    _ = _ := by ring

lemma sourceBranchCombine_bound (α β : ℝ) (v w : H10)
    (hv : SourceSupported v.val) (hw : SourceSupported w.val) {M N : ℝ}
    (hM : 0≤M) (hN : 0≤N)
    (hvM : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x) ≤ M)
    (hwN : ∀ᵐ x∂ballMeasure,abs (weakValue w.val x) ≤ N) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceBranchCombine α β v w).val x) ≤ max (abs α * M) (abs β * N) := by
  filter_upwards [weakValue_add (α • (childZeroTransport 0 v).val) (β • (childZeroTransport 1 w).val),
    weakValue_smul α (childZeroTransport 0 v).val,weakValue_smul β (childZeroTransport 1 w).val,
    childH10Transport_support 0 v hv,childH10Transport_support 1 w hw,
    childH10Transport_bounded 0 v hM hvM,childH10Transport_bounded 1 w hN hwN] with x ha hα hβ hs0 hs1 hb0 hb1
  change abs (weakValue (α • (childZeroTransport 0 v).val+β • (childZeroTransport 1 w).val) x) ≤ _
  rw [ha,Pi.add_apply,hα,hβ,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul]
  by_cases hx : x∈sourceChildEuclidean (actualChildSign 0) '' closure sourceDomain
  · have hn := Set.disjoint_left.mp (source_child_closed_disjoint (show (0:Fin 2)≠1 by decide)) hx
    have he := congrArg jetValue (hs1 hn)
    change weakValue (childZeroTransport 1 w).val x=0 at he
    rw [he,mul_zero,add_zero,abs_mul]
    exact (mul_le_mul_of_nonneg_left hb0 (abs_nonneg α)).trans (le_max_left _ _)
  · have he := congrArg jetValue (hs0 hx)
    change weakValue (childZeroTransport 0 v).val x=0 at he
    rw [he,mul_zero,zero_add,abs_mul]
    exact (mul_le_mul_of_nonneg_left hb1 (abs_nonneg β)).trans (le_max_right _ _)

local instance branchCombinePushAddCommGroup : AddCommGroup (H10 →L[ℝ] H10) :=
  ContinuousLinearMap.addCommGroup (R := ℝ) (R₂ := ℝ) (M := H10) (M₂ := H10)

def sourceAveragePush : H10 →L[ℝ] H10 :=
  (2*sourceScale)⁻¹ • (childZeroTransport 0+childZeroTransport 1)

def sourceDifferencePush : H10 →L[ℝ] H10 :=
  sourceScale⁻¹ • (childZeroTransport 0-childZeroTransport 1)

def sourceAveragePull : H1 →L[ℝ] H1 := (1/2:ℝ) • (childH1Pullback 0+childH1Pullback 1)
def sourceDifferencePull : H1 →L[ℝ] H1 := childH1Pullback 0-childH1Pullback 1

def sourceRatio : ℝ := (2*sourceScale)⁻¹

lemma sourceAveragePush_eq (v : H10) : sourceAveragePush v=sourceBranchCombine sourceRatio sourceRatio v v := by
  change sourceRatio • (childZeroTransport 0 v+childZeroTransport 1 v)=_
  exact smul_add _ _ _

lemma sourceDifferencePush_eq (v : H10) : sourceDifferencePush v=sourceBranchCombine sourceScale⁻¹ (-(sourceScale⁻¹)) v v := by
  change sourceScale⁻¹ • (childZeroTransport 0 v-childZeroTransport 1 v)=_
  change sourceScale⁻¹ • (childZeroTransport 0 v-childZeroTransport 1 v)=sourceScale⁻¹ • childZeroTransport 0 v+(-(sourceScale⁻¹)) • childZeroTransport 1 v
  norm_num [sourceScale]
  module

lemma sourceRatio_pos : 0<sourceRatio := by norm_num [sourceRatio,sourceScale]
lemma sourceRatio_lt_one : sourceRatio<1 := by norm_num [sourceRatio,sourceScale]

lemma sourceAveragePush_support {v : H10} (hv : SourceSupported v.val) :
    SourceSupported (sourceAveragePush v).val := by
  rw [sourceAveragePush_eq]
  exact sourceBranchCombine_support hv hv _ _

lemma sourceDifferencePush_support {v : H10} (hv : SourceSupported v.val) :
    SourceSupported (sourceDifferencePush v).val := by
  rw [sourceDifferencePush_eq]
  exact sourceBranchCombine_support hv hv _ _

lemma sourceAveragePush_energy {v : H10} (hv : SourceSupported v.val) :
    ‖weakGradientL (sourceAveragePush v).val‖^2=sourceRatio*‖weakGradientL v.val‖^2 := by
  rw [sourceAveragePush_eq,sourceBranchCombine_energy _ _ v v hv hv]
  norm_num [sourceRatio,sourceScale]
  ring

lemma sourceDifferencePush_energy {v : H10} (hv : SourceSupported v.val) :
    ‖weakGradientL (sourceDifferencePush v).val‖^2=(2/sourceScale)*‖weakGradientL v.val‖^2 := by
  rw [sourceDifferencePush_eq,sourceBranchCombine_energy _ _ v v hv hv]
  norm_num [sourceScale]
  ring

lemma sourceAveragePush_bound {v : H10} (hv : SourceSupported v.val) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x) ≤ M) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceAveragePush v).val x) ≤ sourceRatio*M := by
  rw [sourceAveragePush_eq]
  simpa only [abs_of_pos sourceRatio_pos,max_self] using sourceBranchCombine_bound sourceRatio sourceRatio v v hv hv hM hM hb hb

lemma sourceDifferencePush_bound {v : H10} (hv : SourceSupported v.val) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x) ≤ M) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceDifferencePush v).val x) ≤ sourceScale⁻¹*M := by
  rw [sourceDifferencePush_eq]
  simpa only [abs_neg,abs_of_pos (show 0<sourceScale⁻¹ by norm_num [sourceScale]),max_self]
    using sourceBranchCombine_bound sourceScale⁻¹ (-(sourceScale⁻¹)) v v hv hv hM hM hb hb

end

open Set MeasureTheory Filter Topology

lemma sourceSupported_zero : SourceSupported (0:H1) := by
  filter_upwards [Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx _
  exact hx

lemma SourceSupported.sum {ι : Type*} (s : Finset ι) (f : ι → H1)
    (hf : ∀ i∈s,SourceSupported (f i)) : SourceSupported (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using sourceSupported_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma sourceSupported_limit {u : ℕ → H1} {w : H1} (hu : Tendsto u atTop (𝓝 w))
    (hs : ∀ n,SourceSupported (u n)) : SourceSupported w := by
  apply h1_limit_ae_closed hu (fun x => {z : JetFiber | x∉closure sourceDomain → z=0}) _ hs
  intro x
  by_cases hx : x∈closure sourceDomain
  · simpa only [hx,not_true_eq_false,false_implies,Set.ofPred_true] using isClosed_univ (X:=JetFiber)
  · simpa only [hx,not_false_eq_true,true_implies] using (isClosed_eq continuous_id continuous_const : IsClosed {z : JetFiber | z = 0})

lemma sourceSupported_collar {u : H1} (hu : SourceSupported u) :
    ∀ᵐ x∂ballMeasure, (5/2:ℝ)<‖x‖ → weakValue u x=0 ∧ weakGradient u x=0 := by
  filter_upwards [(sourceSupported_iff u).mp hu] with x hx hn
  apply hx
  intro hd
  have hd' := sourceClosure_subset_ball hd
  simp only [Metric.mem_ball,dist_zero_right] at hd'
  linarith

def sourceAverageIter (v : H10) : ℕ → H10
  | 0 => v
  | n+1 => sourceAveragePush (sourceAverageIter v n)

lemma sourceAverageIter_support {v : H10} (hv : SourceSupported v.val) (n : ℕ) :
    SourceSupported (sourceAverageIter v n).val := by
  induction n with
  | zero => exact hv
  | succ n ih => exact sourceAveragePush_support ih

lemma sourceAverageIter_energy {v : H10} (hv : SourceSupported v.val) (n : ℕ) :
    ‖weakGradientL (sourceAverageIter v n).val‖^2=sourceRatio^n*‖weakGradientL v.val‖^2 := by
  induction n with
  | zero => simp [sourceAverageIter]
  | succ n ih =>
    change ‖weakGradientL (sourceAveragePush (sourceAverageIter v n)).val‖^2=_
    rw [sourceAveragePush_energy (sourceAverageIter_support hv n),ih,pow_succ]
    ring

lemma sourceAverageIter_bound {v : H10} (hv : SourceSupported v.val) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x)≤M) (n : ℕ) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (sourceAverageIter v n).val x)≤M*sourceRatio^n := by
  induction n with
  | zero => simpa [sourceAverageIter] using hb
  | succ n ih =>
    have hh := sourceAveragePush_bound (sourceAverageIter_support hv n)
      (mul_nonneg hM (pow_nonneg sourceRatio_pos.le n)) ih
    have he : sourceRatio*(M*sourceRatio^n)=M*sourceRatio^(n+1) := by rw [pow_succ]; ring
    simpa only [he,sourceAverageIter] using hh

theorem sourceAverage_series_exists (v : H10) (hv : SourceSupported v.val) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue v.val x)≤M) :
    ∃ w : H10,SourceSupported w.val ∧
      Tendsto (fun N => ∑ n∈Finset.range N,sourceAverageIter v n) atTop (𝓝 w) ∧
      (∀ᵐ x∂ballMeasure,abs (weakValue w.val x)≤(M+‖weakGradientL v.val‖^2)/(1-sourceRatio)) := by
  let K := M+‖weakGradientL v.val‖^2
  have hK : 0≤K := add_nonneg hM (sq_nonneg _)
  obtain ⟨w,hw,ht,hb',hs⟩ := geometric_source_series (fun n => (sourceAverageIter v n).val)
    hK sourceRatio_pos.le sourceRatio_lt_one (fun n => (sourceAverageIter v n).property)
    (fun n => (sourceAverageIter_bound hv hM hb n).mono (fun x hx => hx.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (pow_nonneg sourceRatio_pos.le n))))
    (fun n => by rw [sourceAverageIter_energy hv n]; dsimp [K]; nlinarith [pow_nonneg sourceRatio_pos.le n])
    (5/2) (fun n => sourceSupported_collar (sourceAverageIter_support hv n))
  refine ⟨⟨w,hw⟩,sourceSupported_limit ht (fun n => SourceSupported.sum _ _ (fun i _ => sourceAverageIter_support hv i)),?_,hb'⟩
  apply tendsto_subtype_rng.mpr
  simpa only [Submodule.coe_sum] using ht

end ScalarConductivity

end

end OAI
