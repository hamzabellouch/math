import Mathlib
import OAI.Analysis.Conductivity.Sources.PhysicalMaximum
import OAI.Analysis.Conductivity.Sources.BranchCombine
import OAI.Analysis.Conductivity.Branching.PhysicalTraceTransport

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

namespace BoundedRootSources
variable (r : BoundedRootSources)
def coefficient : R3 → ℝ := copiedScalarCoefficient r.b
lemma coefficient_measurable : Measurable r.coefficient := copiedScalarCoefficient_measurable r.measurable_b
lemma coefficient_bound : ∀ᵐ x∂ballMeasure,abs (r.coefficient x) ≤ max r.C 1 :=
  Eventually.of_forall (fun x => by
    change abs (copiedScalarCoefficient r.b x) ≤ max r.C 1
    rw [abs_of_pos ((lt_min r.c_pos (by norm_num)).trans_le (copiedScalarCoefficient_bounds r.bounds x).1)]
    exact (copiedScalarCoefficient_bounds r.bounds x).2)
def form : H1 →L[ℝ] H1 →L[ℝ] ℝ :=
  energyForm r.coefficient r.coefficient_measurable.aestronglyMeasurable (max r.C 1)
    ((by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)) r.coefficient_bound
lemma form_apply (v h : H1) : r.form v h=energy r.coefficient v h := energyForm_apply _ _ _ _ _ _ _
lemma form_symm (v h : H1) : r.form v h=r.form h v := by
  simp only [form_apply,energy,real_inner_comm]
lemma root_support (j : Fin 2) : SourceSupported (r.W j) :=
  (sourceSupported_iff _).mpr (r.W_support j)
def root (j : Fin 2) : H10 := ⟨r.W j,r.W_H10 j⟩
lemma form_root (j : Fin 2) (h : H1) :
    r.form (r.root j).val h=angularArea*(sourceMeanCLM j.succ h-sourceMeanCLM 0 h) := by
  rw [form_apply]
  exact (r.green r.coefficient (copiedScalarCoefficient_root r.b) j h).trans (basisFlux_mean j h)
lemma form_child (k : Fin 2) (v : H10) (hv : SourceSupported v.val) (h : H1) :
    r.form (childZeroTransport k v).val h=sourceScale*r.form v.val (childH1Pullback k h) := by
  rw [form_apply,form_apply]
  exact copied_child_energy r.b k v hv h
lemma form_average (v : H10) (hv : SourceSupported v.val) (h : H1) :
    r.form (sourceAveragePush v).val h=r.form v.val (sourceAveragePull h) := by
  rw [sourceAveragePush_eq]
  change r.form (sourceRatio • (childZeroTransport 0 v).val+sourceRatio • (childZeroTransport 1 v).val) h=_
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [r.form_child 0 v hv h,r.form_child 1 v hv h]
  change _=r.form v.val ((1/2:ℝ) • (childH1Pullback 0 h+childH1Pullback 1 h))
  rw [map_smul,map_add]
  simp only [smul_eq_mul]
  norm_num [sourceRatio,sourceScale]
  ring
lemma form_difference (v : H10) (hv : SourceSupported v.val) (h : H1) :
    r.form (sourceDifferencePush v).val h=r.form v.val (sourceDifferencePull h) := by
  rw [sourceDifferencePush_eq]
  change r.form (sourceScale⁻¹ • (childZeroTransport 0 v).val+(-(sourceScale⁻¹)) • (childZeroTransport 1 v).val) h=_
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [r.form_child 0 v hv h,r.form_child 1 v hv h]
  change _=r.form v.val (childH1Pullback 0 h-childH1Pullback 1 h)
  rw [map_sub]
  norm_num [sourceScale]
  ring

def sourceHarmonic (u : H1) : Prop := ∀ v : H10,SourceSupported v.val → r.form v.val u=0
lemma harmonic_sourceHarmonic {u : H1} (hu : Harmonic r.coefficient u) : r.sourceHarmonic u := by
  intro v _
  rw [r.form_symm,r.form_apply]
  exact hu v.val v.property
lemma sourceHarmonic_child {u : H1} (hu : r.sourceHarmonic u) (k : Fin 2) :
    r.sourceHarmonic (childH1Pullback k u) := by
  intro v hv
  have he := hu (childZeroTransport k v) (hv.child k)
  rw [r.form_child k v hv] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num [sourceScale])
lemma sourceHarmonic_mean {u : H1} (hu : r.sourceHarmonic u) (k : Fin 2) :
    sourceMeanCLM 0 (childH1Pullback k u)=sourceMeanCLM 0 u := by
  have he := hu (r.root k) (r.root_support k)
  rw [r.form_root,sourceMean_child] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (by dsimp [angularArea]; positivity : angularArea≠0))

end BoundedRootSources
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma weakValue_bound_add {u v : H1} {M N : ℝ}
    (hu : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M)
    (hv : ∀ᵐ x∂ballMeasure,abs (weakValue v x) ≤ N) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (u+v) x) ≤ M+N := by
  filter_upwards [weakValue_add u v,hu,hv] with x he hu hv
  rw [he,Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add hu hv)

lemma weakValue_bound_smul {u : H1} {M : ℝ}
    (hu : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) (a : ℝ) :
    ∀ᵐ x∂ballMeasure,abs (weakValue (a • u) x) ≤ abs a*M := by
  filter_upwards [weakValue_smul a u,hu] with x he hu
  rw [he,Pi.smul_apply,smul_eq_mul,abs_mul]
  exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)

def sourceAveragePullIter : ℕ → H1 →L[ℝ] H1
  | 0 => ContinuousLinearMap.id ℝ H1
  | n+1 => (sourceAveragePullIter n).comp sourceAveragePull

lemma sourceAveragePullIter_succ (n : ℕ) (h : H1) :
    sourceAveragePullIter (n+1) h=sourceAveragePull (sourceAveragePullIter n h) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change sourceAveragePullIter (n+1) (sourceAveragePull h)=sourceAveragePull (sourceAveragePullIter (n+1) h)
    rw [ih]
    rfl

namespace BoundedRootSources
variable (r : BoundedRootSources)

def seed : H10 := (1/(2*angularArea)) • (r.root 0+r.root 1)
def initial : H10 := angularArea⁻¹ • (r.root 0-r.root 1)

lemma seed_support : SourceSupported r.seed.val :=
  ((r.root_support 0).add (r.root_support 1)).smul _
lemma initial_support : SourceSupported r.initial.val := by
  change SourceSupported (angularArea⁻¹ • ((r.root 0).val-(r.root 1).val))
  rw [sub_eq_add_neg,←neg_one_smul ℝ (r.root 1).val]
  exact ((r.root_support 0).add ((r.root_support 1).smul (-1))).smul _

lemma seed_bounded : ∃ M : ℝ,0 ≤ M ∧ ∀ᵐ x∂ballMeasure,abs (weakValue r.seed.val x) ≤ M := by
  have hK : 0 < r.K := r.K_pos
  refine ⟨abs (1/(2*angularArea))*(r.K+r.K),by positivity,?_⟩
  exact weakValue_bound_smul (weakValue_bound_add (r.W_bound 0) (r.W_bound 1)) _
lemma initial_bounded : ∃ M : ℝ,0 ≤ M ∧ ∀ᵐ x∂ballMeasure,abs (weakValue r.initial.val x) ≤ M := by
  have hK : 0 < r.K := r.K_pos
  refine ⟨abs (angularArea⁻¹)*(r.K+abs (-1:ℝ)*r.K),by positivity,?_⟩
  change ∀ᵐ x∂ballMeasure,abs (weakValue (angularArea⁻¹ • (r.W 0-r.W 1)) x) ≤ _
  rw [sub_eq_add_neg,←neg_one_smul ℝ (r.W 1)]
  exact weakValue_bound_smul (weakValue_bound_add (r.W_bound 0) (weakValue_bound_smul (r.W_bound 1) (-1))) _

lemma form_seed (h : H1) :
    r.form r.seed.val h=sourceMeanCLM 0 (sourceAveragePull h)-sourceMeanCLM 0 h := by
  change r.form ((1/(2*angularArea)) • ((r.root 0).val+(r.root 1).val)) h=_
  simp only [map_smul,map_add,smul_apply,add_apply,smul_eq_mul]
  rw [r.form_root,r.form_root,sourceMean_child,sourceMean_child]
  change _=sourceMeanCLM 0 ((1/2:ℝ) • (childH1Pullback 0 h+childH1Pullback 1 h))-sourceMeanCLM 0 h
  rw [map_smul,map_add]
  simp only [smul_eq_mul]
  have hA : angularArea≠0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le angularArea_ge_one)
  field_simp
  ring

lemma form_initial (h : H1) :
    r.form r.initial.val h=sourceMeanCLM 0 (sourceDifferencePull h) := by
  change r.form (angularArea⁻¹ • ((r.root 0).val-(r.root 1).val)) h=_
  simp only [map_smul,map_sub,smul_apply,sub_apply,smul_eq_mul]
  rw [r.form_root,r.form_root,sourceMean_child,sourceMean_child]
  change _=sourceMeanCLM 0 (childH1Pullback 0 h-childH1Pullback 1 h)
  rw [map_sub]
  have hA : angularArea≠0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le angularArea_ge_one)
  field_simp
  ring

lemma form_averageIter (v : H10) (hv : SourceSupported v.val) (n : ℕ) (h : H1) :
    r.form (sourceAverageIter v n).val h=r.form v.val (sourceAveragePullIter n h) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change r.form (sourceAveragePush (sourceAverageIter v n)).val h=_
    rw [r.form_average _ (sourceAverageIter_support hv n),ih]
    rfl

def finiteSource (N : ℕ) : H10 :=
  r.initial+sourceDifferencePush (∑ n∈Finset.range N,sourceAverageIter r.seed n)

lemma finiteSource_support (N : ℕ) : SourceSupported (r.finiteSource N).val := by
  apply r.initial_support.add
  apply sourceDifferencePush_support
  simp only [Submodule.coe_sum]
  exact SourceSupported.sum _ _ (fun n _ => sourceAverageIter_support r.seed_support n)

lemma form_finiteSource (N : ℕ) (h : H1) :
    r.form (r.finiteSource N).val h=sourceMeanCLM 0 (sourceAveragePullIter N (sourceDifferencePull h)) := by
  induction N with
  | zero =>
    change r.form (r.initial+sourceDifferencePush (∑ n∈Finset.range 0,sourceAverageIter r.seed n)).val h=_
    simpa only [Finset.range_zero,Finset.sum_empty,map_zero,add_zero,sourceAveragePullIter,ContinuousLinearMap.id_apply] using r.form_initial h
  | succ N ih =>
    have he : r.finiteSource (N+1)=r.finiteSource N+sourceDifferencePush (sourceAverageIter r.seed N) := by
      simp only [finiteSource,Finset.sum_range_succ,map_add,add_assoc]
    rw [he]
    change r.form ((r.finiteSource N).val+(sourceDifferencePush (sourceAverageIter r.seed N)).val) h=_
    rw [map_add,add_apply,ih,r.form_difference _ (sourceAverageIter_support r.seed_support N),
      r.form_averageIter r.seed r.seed_support N,r.form_seed,sourceAveragePullIter_succ]
    ring

theorem nested_source_limit_exists : ∃ w : H10,SourceSupported w.val ∧
    (∃ M : ℝ,0<M ∧ ∀ᵐ x∂ballMeasure,abs (weakValue w.val x) ≤ M) ∧
    Tendsto (fun N => (r.finiteSource N).val) atTop (𝓝 w.val) := by
  obtain ⟨M,hM,hb⟩ := r.seed_bounded
  obtain ⟨v,hv,ht,hvb⟩ := sourceAverage_series_exists r.seed r.seed_support hM hb
  let w : H10 := r.initial+sourceDifferencePush v
  have hw : SourceSupported w.val := r.initial_support.add (sourceDifferencePush_support hv)
  obtain ⟨P,hP,hPb⟩ := r.initial_bounded
  let Q := (M+‖weakGradientL r.seed.val‖^2)/(1-sourceRatio)
  have hQ : 0 ≤ Q := div_nonneg (add_nonneg hM (sq_nonneg _)) (sub_nonneg.mpr sourceRatio_lt_one.le)
  have hDb := sourceDifferencePush_bound hv hQ hvb
  have hs : 0 < sourceScale := by norm_num [sourceScale]
  refine ⟨w,hw,⟨P+sourceScale⁻¹*Q+1,by positivity,?_⟩,?_⟩
  · exact (weakValue_bound_add hPb hDb).mono (fun x hx => hx.trans (by linarith))
  · have : ContinuousAdd H10 := (Submodule.isTopologicalAddGroup H10).toContinuousAdd
    have htw : Tendsto (fun N => r.finiteSource N) atTop (𝓝 w) :=
      (tendsto_const_nhds (x := r.initial)).add ((sourceDifferencePush.continuous.continuousAt.tendsto).comp ht)
    exact continuous_subtype_val.continuousAt.tendsto.comp htw

end BoundedRootSources
end ScalarConductivity

end
end

end OAI
