import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.AdaptiveReveal

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct

def DecisionCode : ℕ → Type
  | 0 => Unit
  | n+1 => DecisionCode n×Bool

instance (n : ℕ) : Fintype (DecisionCode n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (DecisionCode n×Bool))

structure DecisionRule (E S : Type*) where
  initial : S
  block : S → Set E
  further : ℕ → S → Set E
  contained : ∀ n s, block s⊆further n s
  active : ℕ → S → Prop
  accept : ℕ → S → Set (Set E)
  measurable : ∀ n s, MeasurableSet[blockSigma (further n s)] (accept n s)
  update : ℕ → S → Bool → S
  block_update : ∀ n s b, block (update n s b)=further n s

namespace DecisionRule
variable {E S : Type*} (D : DecisionRule E S)

def state : (n : ℕ) → DecisionCode n → S
  | 0,_ => D.initial
  | n+1,(w,b) => D.update n (state n w) b

def partitionWithBlock : (n : ℕ) →
    {P : RevealPartition E (DecisionCode n) // ∀ w, P.block w=D.block (D.state n w)}
  | 0 => ⟨{
      block := fun _ => D.block D.initial
      cell := fun _ => Set.univ
      measurable := fun _ => MeasurableSet.univ
      disjoint := by intro i j hne; have he : i=j := @Subsingleton.elim Unit _ i j; exact (hne he).elim
      cover := Set.eq_univ_of_forall (fun _ => Set.mem_iUnion.mpr ⟨(),Set.mem_univ _⟩) },
      fun _ => rfl⟩
  | n+1 => by
      let P := (partitionWithBlock n).val
      have hP := (partitionWithBlock n).property
      let Q := P.enlarge (fun w => D.further n (D.state n w)) (by
        intro w
        rw [hP w]
        exact D.contained n (D.state n w))
      let T := Q.decide (fun w ω => if ω∈D.accept n (D.state n w) then true else false) (by
        intro w
        exact Measurable.ite (D.measurable n (D.state n w)) measurable_const measurable_const)
      refine ⟨T,?_⟩
      intro w
      change D.further n (D.state n w.1)=D.block (D.update n (D.state n w.1) w.2)
      exact (D.block_update n _ _).symm

def partition (n : ℕ) : RevealPartition E (DecisionCode n) :=
  (D.partitionWithBlock n).val

lemma partition_block (n : ℕ) (w : DecisionCode n) :
    (D.partition n).block w=D.block (D.state n w) :=
  (D.partitionWithBlock n).property w

lemma partition_cell_succ (n : ℕ) (w : DecisionCode n) (b : Bool) :
    (D.partition (n+1)).cell (w,b)=(D.partition n).cell w∩
      {ω | (if ω∈D.accept n (D.state n w) then true else false)=b} := rfl

lemma historySigma_step (n : ℕ) : (D.partition n).historySigma ≤ (D.partition (n+1)).historySigma := by
  intro A hA w
  rcases w with ⟨w,b⟩
  change MeasurableSet[blockSigma (D.further n (D.state n w))]
    (A ∩ ((D.partition n).cell w ∩
      {ω | (if ω∈D.accept n (D.state n w) then true else false)=b}))
  rw [← Set.inter_assoc]
  have hmono : blockSigma (D.block (D.state n w)) ≤ blockSigma (D.further n (D.state n w)) :=
    iSup₂_mono' (fun e he => ⟨e,D.contained n (D.state n w) he,le_rfl⟩)
  refine (hmono _ ?_).inter ?_
  · rw [← D.partition_block n w]
    exact hA w
  · have hm : @Measurable (Set E) Bool (blockSigma (D.further n (D.state n w))) inferInstance
        (fun ω => if ω∈D.accept n (D.state n w) then true else false) :=
      Measurable.ite (D.measurable n (D.state n w)) measurable_const measurable_const
    exact hm (MeasurableSet.singleton b)

lemma historySigma_mono : Monotone (fun n => (D.partition n).historySigma) :=
  monotone_nat_of_le_succ D.historySigma_step

def failure (n : ℕ) : Set (Set E) := ⋃ w : DecisionCode n,
  (D.partition n).cell w∩{ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)}

lemma failure_on_cell (n : ℕ) {w : DecisionCode n} {ω : Set E}
    (hw : ω∈(D.partition n).cell w) :
    ω∈D.failure n ↔ D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w) := by
  constructor
  · intro h
    obtain ⟨v,hv,hf⟩ := Set.mem_iUnion.mp h
    have he := (D.partition n).cell_unique hv hw
    change D.active n (D.state n v) ∧ ω∉D.accept n (D.state n v) at hf
    simpa only [he] using hf
  · intro h
    exact Set.mem_iUnion.mpr ⟨w,hw,h⟩

lemma failure_measurable (n : ℕ) : MeasurableSet (D.failure n) := by
  apply MeasurableSet.iUnion
  intro w
  exact ((D.partition n).cell_measurable w).inter
    ((MeasurableSet.const _).inter ((blockSigma_le _) _ (D.measurable n (D.state n w))).compl)

lemma failure_history_measurable (n : ℕ) :
    MeasurableSet[(D.partition (n+1)).historySigma] (D.failure n) := by
  intro w
  rcases w with ⟨w,b⟩
  have he : D.failure n∩(D.partition (n+1)).cell (w,b)=
      {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)}∩
        (D.partition (n+1)).cell (w,b) := by
    ext ω
    constructor <;> intro h
    · exact ⟨(D.failure_on_cell n (by rw [D.partition_cell_succ] at h; exact h.2.1)).mp h.1,h.2⟩
    · exact ⟨(D.failure_on_cell n (by rw [D.partition_cell_succ] at h; exact h.2.1)).mpr h.1,h.2⟩
  rw [he]
  apply MeasurableSet.inter _ ((D.partition (n+1)).measurable (w,b))
  change MeasurableSet[blockSigma (D.further n (D.state n w))] _
  exact (MeasurableSet.const _).inter (D.measurable n (D.state n w)).compl

lemma failure_probability_on_cell (q : E → unitInterval) (n : ℕ)
    {w : DecisionCode n} {σ : Set E} (hw : σ∈(D.partition n).cell w) :
    blockProbability q ((D.partition n).block w) (D.failure n) σ=
      blockProbability q (D.block (D.state n w))
        {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)} σ := by
  rw [← D.partition_block n w]
  unfold blockProbability
  congr 1
  ext ω
  apply D.failure_on_cell
  exact (block_event_forceOn _ _ ((D.partition n).measurable w) σ ω).mpr hw

theorem conditional_failure_bound (q : E → unitInterval) (B : Set (Set E))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ n w σ, σ∈(D.partition n).cell w → σ∈B →
      (blockProbability q (D.block (D.state n w))
        {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)} σ).toReal ≤ ε) :
    ∀ n A, MeasurableSet[(D.partition n).historySigma] A → A⊆B →
      (law q).real (A∩D.failure n) ≤ ε*(law q).real A := by
  intro n A hmA hAB
  apply (D.partition n).measureReal_inter_le q (D.failure n) A (D.failure_measurable n) hmA ε hε
  intro σ hσ
  obtain ⟨w,hw⟩ := (D.partition n).exists_cell σ
  rw [(D.partition n).probability_on_cell q (D.failure n) hw,D.failure_probability_on_cell q n hw]
  exact (ENNReal.toReal_le_toReal (ne_of_lt (lt_of_le_of_lt (blockProbability_le_one _ _ _ _) ENNReal.one_lt_top))
    ENNReal.ofReal_ne_top).mp (by rw [ENNReal.toReal_ofReal hε]; exact hlocal n w σ hw (hAB hσ))

def codeOf : (n : ℕ) → Set E → DecisionCode n
  | 0,_ => ()
  | n+1,ω => (codeOf n ω,if ω∈D.accept n (D.state n (codeOf n ω)) then true else false)

lemma codeOf_mem (n : ℕ) (ω : Set E) : ω∈(D.partition n).cell (D.codeOf n ω) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,rfl⟩

lemma codeOf_eq_of_mem {n : ℕ} {w : DecisionCode n} {ω : Set E}
    (h : ω∈(D.partition n).cell w) : D.codeOf n ω=w :=
  (D.partition n).cell_unique (D.codeOf_mem n ω) h

end DecisionRule
end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
