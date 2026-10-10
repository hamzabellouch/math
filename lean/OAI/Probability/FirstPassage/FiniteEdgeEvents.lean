import OAI.Probability.FirstPassage.Translation

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset

def DependsOnEdges (A : Set (Edge → ℝ)) (S : Finset Edge) : Prop :=
  ∀ w w', (∀ e ∈ S, w e=w' e) → (w ∈ A ↔ w' ∈ A)

noncomputable def extendEdgeWeights (S : Finset Edge) (w : S → ℝ) : Edge → ℝ :=
  fun e => if he : e ∈ S then w ⟨e,he⟩ else 0

theorem measurable_extendEdgeWeights (S : Finset Edge) : Measurable (extendEdgeWeights S) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ S
  · simpa only [extendEdgeWeights,dite_eq_left he] using (measurable_pi_apply (⟨e,he⟩ : S))
  · simp only [extendEdgeWeights,dite_eq_right he]
    exact measurable_const

theorem DependsOnEdges.restriction_iff {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    extendEdgeWeights S (fun e : S => w e) ∈ A ↔ w ∈ A := by
  apply hA
  intro e he
  simp [extendEdgeWeights,he]

theorem DependsOnEdges.compl {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) : DependsOnEdges Aᶜ S := by
  intro w w' hh
  exact not_congr (hA w w' hh)

theorem dependsOnEdges_biInter {ι : Type*} (t : Finset ι)
    (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, DependsOnEdges (A i) (S i)) :
    DependsOnEdges (⋂ i ∈ t, A i) (t.biUnion S) := by
  classical
  intro w w' hh
  simp only [mem_iInter]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact hA i hi w w' (fun e he => hh e (mem_biUnion.mpr ⟨i,hi,he⟩))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem disjoint_edge_events_independent (h : ExponentialEnvironment P τ)
    (A B : Set (Edge → ℝ)) (S T : Finset Edge)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : DependsOnEdges A S) (hBT : DependsOnEdges B T) (hST : Disjoint S T) :
    IndepSet {ω | (fun e => τ e ω) ∈ A} {ω | (fun e => τ e ω) ∈ B} P := by
  let _ := h.probability
  have hf := h.independent.indepFun_finset S T hST h.measurable
  have hs : Measurable (fun ω (e : S) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have ht : Measurable (fun ω (e : T) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have hi := (indepFun_iff_indepSet_preimage hs ht).mp hf
    ((extendEdgeWeights S) ⁻¹' A) ((extendEdgeWeights T) ⁻¹' B)
    (hA.preimage (measurable_extendEdgeWeights S)) (hB.preimage (measurable_extendEdgeWeights T))
  have heA : (fun ω (e : S) => τ e ω) ⁻¹' ((extendEdgeWeights S) ⁻¹' A) =
      {ω | (fun e => τ e ω) ∈ A} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hAS.restriction_iff (fun e => τ e ω)
  have heB : (fun ω (e : T) => τ e ω) ⁻¹' ((extendEdgeWeights T) ⁻¹' B) =
      {ω | (fun e => τ e ω) ∈ B} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hBT.restriction_iff (fun e => τ e ω)
  simpa only [heA,heB] using hi

theorem disjoint_edge_events_inter_probability (h : ExponentialEnvironment P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j))) :
    P {ω | ∀ i ∈ t, (fun e => τ e ω) ∈ A i} =
      ∏ i ∈ t, P {ω | (fun e => τ e ω) ∈ A i} := by
  classical
  let _ := h.probability
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hAt : ∀ i ∈ t, MeasurableSet (A i) := fun i hi => hA i (mem_insert_of_mem hi)
    have hSt : ∀ i ∈ t, DependsOnEdges (A i) (S i) := fun i hi => hAS i (mem_insert_of_mem hi)
    have hd : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)) := by
      intro i hi j hj hij
      exact hdis (mem_insert_of_mem hi) (mem_insert_of_mem hj) hij
    have hdunion : Disjoint (S a) (t.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hi) (by intro he; exact ha (he ▸ hi))
    have hm : MeasurableSet (⋂ i ∈ t, A i) := MeasurableSet.biInter (t.countable_toSet) hAt
    have hi := disjoint_edge_events_independent h (A a) (⋂ i ∈ t, A i) (S a) (t.biUnion S)
      (hA a (mem_insert_self _ _)) hm (hAS a (mem_insert_self _ _))
      (dependsOnEdges_biInter t A S hSt) hdunion
    have hprob := hi.measure_inter_eq_mul
    have he : {ω | ∀ i ∈ insert a t, (fun e => τ e ω) ∈ A i} =
        {ω | (fun e => τ e ω) ∈ A a} ∩ {ω | (fun e => τ e ω) ∈ ⋂ i ∈ t, A i} := by
      ext ω; simp
    rw [he,hprob,Finset.prod_insert ha]
    congr 1
    simpa only [mem_iInter] using ih hAt hSt hd

theorem disjoint_edge_events_iIndepSet (h : ExponentialEnvironment P τ)
    {ι : Type*} (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i, MeasurableSet (A i)) (hAS : ∀ i, DependsOnEdges (A i) (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndepSet (fun i => {ω | (fun e => τ e ω) ∈ A i}) P := by
  apply (iIndepSet_iff_meas_biInter (fun i => (hA i).preimage
    (Measurable.of_eval h.measurable))).mpr
  intro t
  simpa only [ofPred_forall,Set.preimage] using disjoint_edge_events_inter_probability h t A S
    (fun i _ => hA i) (fun i _ => hAS i) (fun i _ j _ hij => hdis hij)

theorem disjoint_trials_failure_bound (h : ExponentialEnvironment P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)))
    (p : ℝ)
    (hprob : ∀ i ∈ t, p ≤ P.real {ω | (fun e => τ e ω) ∈ A i}) :
    P.real {ω | ∀ i ∈ t, (fun e => τ e ω) ∉ A i} ≤ (1-p)^t.card := by
  classical
  let _ := h.probability
  have he := disjoint_edge_events_inter_probability h t (fun i => (A i)ᶜ) S
    (fun i hi => (hA i hi).compl) (fun i hi => (hAS i hi).compl) hdis
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_prod] at her
  change P.real _ = ∏ i ∈ t, P.real {ω | (fun e => τ e ω) ∉ A i} at her
  simp only [mem_compl_iff] at her
  rw [her]
  calc
    _ ≤ ∏ _i ∈ t, (1-p) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact measureReal_nonneg
      · intro i hi
        have hm := (hA i hi).preimage (Measurable.of_eval h.measurable)
        have hc := measureReal_compl (μ := P) hm
        simp only [Set.preimage] at hc
        change P.real ({ω | (fun e => τ e ω) ∈ A i}ᶜ) ≤ _
        rw [hc]
        simpa using sub_le_sub_left (hprob i hi) 1
    _ = _ := by simp

end PlanarFPP

end OAI
