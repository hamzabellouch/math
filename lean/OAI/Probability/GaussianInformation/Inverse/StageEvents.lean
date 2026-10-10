import Mathlib
import OAI.Probability.GaussianInformation.Inverse.DyadicBins

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma measure_sequential_event_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (a : α) :
    ∀ k : ℕ,∀ (P : Fin k → (Fin k → α) → Prop) (B : Fin k → ℝ≥0∞),
    (∀ i,MeasurableSet {z | P i z}) →
    (∀ i f g,(∀ j,j ≤ i → f j=g j) → (P i f ↔ P i g)) →
    (∀ i f,μ {x | P i (Function.update f i x)} ≤ B i) →
    (Measure.pi (fun _ : Fin k => μ)) {z | ∀ i,P i z} ≤ ∏ i,B i := by
  classical
  intro k
  induction k with
  | zero => intro P B _ _ _; simp
  | succ k ih =>
    intro P B hP hdep hcond
    let P' : Fin k → (Fin k → α) → Prop := fun i z => P i.castSucc (Fin.snoc z a)
    let B' : Fin k → ℝ≥0∞ := fun i => B i.castSucc
    have hP' : ∀ i,MeasurableSet {z | P' i z} := fun i =>
      (hP i.castSucc).preimage (measurable_snoc_const a)
    have hdep' : ∀ i f g,(∀ j,j ≤ i → f j=g j) → (P' i f ↔ P' i g) := by
      intro i f g hfg
      apply hdep
      intro j
      refine Fin.lastCases ?_ (fun l => ?_) j
      · intro hj
        exact (not_le_of_gt (Fin.castSucc_lt_last i) hj).elim
      · intro hj
        simp only [Fin.snoc_castSucc]
        exact hfg l (by simpa only [Fin.castSucc_le_castSucc_iff] using hj)
    have hcond' : ∀ i f,μ {x | P' i (Function.update f i x)} ≤ B' i := by
      intro i f
      simpa only [P',B',Fin.snoc_update] using hcond i.castSucc (Fin.snoc f a)
    have hind := ih P' B' hP' hdep' hcond'
    let E : Set (Fin (k+1) → α) := {z | ∀ i,P i z}
    let E' : Set (Fin k → α) := {z | ∀ i,P' i z}
    have hE : MeasurableSet E := by simpa [E,Set.ofPred_forall] using MeasurableSet.iInter (fun i => hP i)
    have hE' : MeasurableSet E' := by simpa [E',Set.ofPred_forall] using MeasurableSet.iInter (fun i => hP' i)
    have hbefore : ∀ (z : Fin k → α) (x : α) (i : Fin k),
        P i.castSucc (Fin.snoc z x) ↔ P' i z := by
      intro z x i
      apply hdep
      intro j
      refine Fin.lastCases ?_ (fun l => ?_) j
      · intro hj
        exact (not_le_of_gt (Fin.castSucc_lt_last i) hj).elim
      · intro _; simp
    have hleaf : ∀ z : Fin k → α,
        μ {x | Fin.snoc z x ∈ E} ≤ E'.indicator (fun _ => B (Fin.last k)) z := by
      intro z
      by_cases hz : z∈E'
      · rw [indicator_of_mem hz]
        calc
          _ ≤ μ {x | P (Fin.last k) (Fin.snoc z x)} := by
            apply measure_mono
            intro x hx
            change (∀ i,P i (Fin.snoc z x)) at hx
            exact hx (Fin.last k)
          _ ≤ B (Fin.last k) := by simpa only [snoc_update_last] using hcond (Fin.last k) (Fin.snoc z a)
      · rw [indicator_of_notMem hz]
        have hempty : {x | Fin.snoc z x ∈ E}=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          apply hz
          intro i
          exact (hbefore z x i).mp (hx i.castSucc)
        simp [hempty]
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) (Fin.last k)).symm
    have heq : (Measure.pi (fun _ : Fin (k+1) => μ)) E =
        ∫⁻ z : Fin k → α,μ {x | Fin.snoc z x ∈ E} ∂Measure.pi (fun _ => μ) := by
      rw [← hp.measure_preimage hE.nullMeasurableSet,Measure.prod_apply_symm (hE.preimage hp.measurable)]
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
        Fin.insertNth_last]
      rfl
    change (Measure.pi (fun _ : Fin (k+1) => μ)) E ≤ _
    rw [heq]
    calc
      _ ≤ ∫⁻ z : Fin k → α,E'.indicator (fun _ => B (Fin.last k)) z ∂Measure.pi (fun _ => μ) := lintegral_mono hleaf
      _ = B (Fin.last k)*(Measure.pi (fun _ : Fin k => μ)) E' := by
        rw [lintegral_indicator hE',lintegral_const,Measure.restrict_apply_univ]
      _ ≤ B (Fin.last k)*∏ i,B' i := mul_le_mul_right hind _
      _ = ∏ i,B i := by rw [Fin.prod_univ_castSucc]; simp only [B']; ring
noncomputable def translated {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d) : Fin k → Ambient d :=
  fun i => z i-u

lemma measurable_translated {d k : ℕ} (u : Ambient d) : Measurable (translated (k := k) u) :=
  Measurable.of_eval (fun i => (measurable_pi_apply i).sub measurable_const)

noncomputable def StageEvent {d k : ℕ} (u : Ambient d) (l : Fin k → ℤ) (i : Fin k)
    (z : Fin k → Ambient d) : Prop :=
  0 ≤ l i → z i-u∈groupedTube (prefixAxes (translated u z) i) (binGap l i) (dyadicRadius (l i))

lemma measurable_translated_residual {d k : ℕ} (u : Ambient d) (i : Fin k) :
    Measurable (fun z : Fin k → Ambient d => residual (prefixAxes (translated u z) i) (z i-u)) := by
  have hm : Measurable (fun z : Fin k → Ambient d => (translated u z,z i-u)) :=
    (measurable_translated (k := k) u).prodMk ((measurable_pi_apply i).sub measurable_const)
  simpa only [prefixResidual_eq,Function.comp_def] using (measurable_prefixResidual (d := d) i).comp hm

lemma measurable_translated_coefficient {d k : ℕ} (u : Ambient d) (i j : Fin k) :
    Measurable (fun z : Fin k → Ambient d => inner ℝ (prefixAxes (translated u z) i j) (z i-u)) := by
  have ha : Measurable (fun z : Fin k → Ambient d => prefixAxes (translated u z) i j) :=
    (measurable_prefixAxes (d := d) i j).comp (measurable_translated u)
  exact ha.inner (𝕜 := ℝ) ((measurable_pi_apply i).sub measurable_const)

lemma measurableSet_stageEvent {d k : ℕ} (u : Ambient d) (l : Fin k → ℤ) (i : Fin k) :
    MeasurableSet {z | StageEvent u l i z} := by
  classical
  by_cases hi : 0 ≤ l i
  · have hr := measurable_translated_residual u i
    have hs : ∀ h : ℕ,Measurable (fun z : Fin k → Ambient d =>
        ∑ j ∈ Finset.univ.filter (fun j => binGap l i j=h),
          (inner ℝ (prefixAxes (translated u z) i j) (z i-u))^2) := by
      intro h
      apply Finset.measurable_sum
      intro j _
      exact (measurable_translated_coefficient u i j).pow_const _
    simp only [StageEvent,hi,forall_true_left]
    change MeasurableSet {z : Fin k → Ambient d |
      ‖residual (prefixAxes (translated u z) i) (z i-u)‖ ≤ dyadicRadius (l i) ∧
      ∀ h : ℕ,∑ j ∈ Finset.univ.filter (fun j => binGap l i j=h),
        (inner ℝ (prefixAxes (translated u z) i j) (z i-u))^2 ≤ (dyadicRadius (l i))^2*4^h}
    rw [ofPred_and]
    apply MeasurableSet.inter (measurableSet_le hr.norm measurable_const)
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun h => measurableSet_le (hs h) measurable_const)
  · simp [StageEvent,hi]

lemma stageEvent_prefix {d k : ℕ} (u : Ambient d) (l : Fin k → ℤ) (i : Fin k)
    (f g : Fin k → Ambient d) (hfg : ∀ j,j  ≤  i → f j=g j) :
    StageEvent u l i f ↔ StageEvent u l i g := by
  have he : prefixAxes (translated u f) i=prefixAxes (translated u g) i :=
    prefixAxes_prefix_congr i (fun j hj => congrArg (fun x => x-u) (hfg j hj.le))
  simp only [StageEvent,he,hfg i le_rfl]

lemma stageEvent_update {d k : ℕ} (u : Ambient d) (l : Fin k → ℤ) (i : Fin k)
    (f : Fin k → Ambient d) (x : Ambient d) :
    StageEvent u l i (Function.update f i x) ↔
      (0 ≤ l i → x-u∈groupedTube (prefixAxes (translated u f) i) (binGap l i) (dyadicRadius (l i))) := by
  have he : prefixAxes (translated u (Function.update f i x)) i=prefixAxes (translated u f) i := by
    apply prefixAxes_prefix_congr
    intro j hj
    simp only [translated,Function.update_of_ne (ne_of_lt hj)]
  simp only [StageEvent,he,Function.update_self]

lemma greedy_bins_stageEvents {d k : ℕ} {ε : ℝ} (u : Ambient d) {z : Fin k → Ambient d}
    {l : Fin k → ℤ} (hg : Greedy residualScore (translated u z))
    (hl : InBins ε (translated u z) l) : ∀ i,StageEvent u l i z :=
  fun i _ => greedy_mem_groupedTube hg hl i

end AllScaleInverseVolume

end OAI
