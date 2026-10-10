import Mathlib
import OAI.Probability.Ballisticity.Estimates.AdaptiveFailureWeights
import OAI.Probability.Ballisticity.Estimates.BufferChildNode

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferNodeAt {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) : List (ℕ × Bool) → AdaptedBufferNode e
  | [] => root
  | p::l => let N := bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l
    bufferChildNode e f hef R₀ z₀ ε α g κ N (H N.radius) (hH N.radius) p.1 p.2

lemma bufferNodeAt_radius {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (hr : R₀ ≤ root.radius) (l : List (ℕ × Bool)) :
    R₀ ≤ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).radius := by
  cases l with
  | nil => exact hr
  | cons p l => exact le_max_left _ _

lemma bufferNodeAt_valid {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (z₀ ε α g : ℝ) {κ : ℝ≥0}
    (hκpos : 0 < κ) (hκ1 : κ ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 ≤ ε)
    (H : ℝ → ℕ) (hH : ∀ r, 0 < H r) (root : AdaptedBufferNode e)
    (hr : R₀ ≤ root.radius) (hroot : BufferNodeValid e f z₀ κ root) (l : List (ℕ × Bool)) :
    BufferNodeValid e f z₀ κ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l) := by
  induction l with
  | nil => exact hroot
  | cons p l ih =>
    exact bufferChildNode_valid e f hef R₀ z₀ ε α g hκpos hκ1 hg hg1 hε _
      (hR₀.trans (bufferNodeAt_radius e f hef R₀ z₀ ε α g κ H hH root hr l)) ih _ (hH _) p.1 p.2

noncomputable def bufferNodeDecision {d : ℕ} (e f : Direction d)
    (z₀ ε α g : ℝ) (H : ℝ → ℕ) (N : AdaptedBufferNode e) (ω : Environment d) : ℕ × Bool :=
  (bufferFirstFailure (realPosition (step e)) f N.level (z₀+(1-ε)*N.radius) g N.law (H N.radius) ω,
    decide (BufferStageEvent (realPosition (step e)) f (H N.radius) z₀ N.radius ε α g (N.law ω).val ω))

lemma mem_bufferChildNode_iff {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (N : AdaptedBufferNode e) (p : ℕ × Bool) (ω : Environment d) :
    ω ∈ (bufferChildNode e f hef R₀ z₀ ε α g κ N (H N.radius) (hH N.radius) p.1 p.2).active ↔
      ω ∈ N.active ∧ bufferNodeDecision e f z₀ ε α g H N ω=p := by
  change (_ ∧ _ ∧ (_ ↔ p.2=true)) ↔ (_ ∧ (_,decide _)=p)
  rw [Prod.ext_iff]
  suffices (BufferStageEvent (realPosition (step e)) f (H N.radius) z₀ N.radius ε α g (N.law ω).val ω ↔ p.2=true) ↔
      decide (BufferStageEvent (realPosition (step e)) f (H N.radius) z₀ N.radius ε α g (N.law ω).val ω)=p.2 by tauto
  cases p.2 <;> simp

noncomputable def bufferHistory {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) : ℕ → List (ℕ × Bool)
  | 0 => []
  | n+1 => let l := bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n
    bufferNodeDecision e f z₀ ε α g H (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l) ω :: l

lemma bufferHistory_length {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (n : ℕ) :
    (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bufferHistory,List.length_cons,ih]

lemma bufferNodeAt_active_iff_history {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (l : List (ℕ × Bool)) :
    ω ∈ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).active ↔
      ω ∈ root.active ∧ bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω l.length=l := by
  induction l with
  | nil => simp only [bufferNodeAt,bufferHistory,List.length_nil,and_true]
  | cons p l ih =>
    rw [bufferNodeAt,mem_bufferChildNode_iff e f hef R₀ z₀ ε α g κ H hH
      (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l) p ω,ih]
    simp only [List.length_cons,bufferHistory,List.cons.injEq]
    constructor
    · rintro ⟨⟨hr,hl⟩,hp⟩
      exact ⟨hr,by simpa only [hl] using hp,hl⟩
    · rintro ⟨hr,hp,hl⟩
      exact ⟨⟨hr,hl⟩,by simpa only [hl] using hp⟩
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev BufferWords (n : ℕ) := {l : List (ℕ × Bool) // l.length=n}

noncomputable def bufferTreeSuccess {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (n : ℕ) : Set (Environment d) :=
  ⋃ l : BufferWords n, {ω | ω ∈ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).active ∧
    (bufferNodeDecision e f z₀ ε α g H (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val) ω).2=true}

lemma bufferTreeSuccess_measurable {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (n : ℕ) :
    MeasurableSet (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root n) := by
  apply MeasurableSet.iUnion
  intro l
  let N := bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val
  have ha : MeasurableSet N.active := rowSigma_le _ _ N.active_rows
  have hp : Measurable N.law := N.law_rows.mono (rowSigma_le _) le_rfl
  have he := (measurableSet_bufferStageEvent_rows (realPosition (step e)) f (hH N.radius)
    z₀ N.radius ε α g (PairAtHeight (realPosition (step e)) N.level) Set.univ
    (fun x hx => ⟨Set.subset_univ _,Set.subset_univ _⟩)).preimage
      (hp.prodMk (measurable_id.mono le_rfl (rowSigma_le Set.univ)))
  convert ha.inter he using 1
  ext ω
  simp only [bufferNodeDecision,decide_eq_true_eq,Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,id_eq]
  rfl

lemma bufferWords_partition {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (n : ℕ) :
    (⋃ l : BufferWords n, (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).active) = root.active ∧
    Pairwise (Disjoint on fun l : BufferWords n =>
      (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).active) := by
  constructor
  · ext ω
    constructor
    · intro h
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp h
      exact (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mp hl |>.1
    · intro hr
      let l : BufferWords n := ⟨bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n,
        bufferHistory_length e f hef R₀ z₀ ε α g κ H hH root ω n⟩
      apply Set.mem_iUnion.mpr
      refine ⟨l,(bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mpr ?_⟩
      exact ⟨hr,by rw [l.property]⟩
  · intro l m hlm
    apply Set.disjoint_left.mpr
    intro ω hl hm
    apply hlm
    apply Subtype.ext
    have hl' := (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mp hl |>.2
    have hm' := (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω m.val).mp hm |>.2
    rw [l.property] at hl'
    rw [m.property] at hm'
    exact hl'.symm.trans hm'

lemma bufferTreeSuccess_iff_decision {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (hr : ω ∈ root.active) (n : ℕ) :
    ω ∈ bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root n ↔
      (bufferNodeDecision e f z₀ ε α g H (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root
        (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n)) ω).2=true := by
  constructor
  · intro h
    obtain ⟨l,hl,hb⟩ := Set.mem_iUnion.mp h
    have hh := (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mp hl |>.2
    rw [l.property] at hh
    simpa only [hh] using hb
  · intro hb
    let l : BufferWords n := ⟨bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n,
      bufferHistory_length e f hef R₀ z₀ ε α g κ H hH root ω n⟩
    apply Set.mem_iUnion.mpr
    refine ⟨l,?_,hb⟩
    apply (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mpr
    exact ⟨hr,by rw [l.property]⟩

noncomputable def bufferWordSuccesses : List (ℕ × Bool) → ℝ
  | [] => 0
  | p::l => (if p.2 then 1 else 0)+bufferWordSuccesses l

lemma bufferWordSuccesses_history {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (hr : ω ∈ root.active) (n : ℕ) :
    bufferWordSuccesses (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n) =
      successes (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root) n ω := by
  induction n with
  | zero => simp [bufferHistory,bufferWordSuccesses,successes]
  | succ n ih =>
    rw [bufferHistory,bufferWordSuccesses,ih,successes_succ]
    have hb := bufferTreeSuccess_iff_decision e f hef R₀ z₀ ε α g κ H hH root ω hr n
    simp only [←hb]
    ring

lemma buffer_failureWeight_on_branch {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (s : ℝ) (n : ℕ) (l : BufferWords n) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e))
      (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).level)) _
      ((bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).active.indicator
        (fun ω => ENNReal.ofReal (failureWeight (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root) s n ω))) := by
  let N := bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val
  have he : N.active.indicator (fun ω => ENNReal.ofReal (failureWeight
      (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root) s n ω)) =
      N.active.indicator (fun _ => ENNReal.ofReal (Real.exp (s/4*(n:ℝ)-bufferWordSuccesses l.val))) := by
    apply Set.indicator_congr
    intro ω hω
    have hh := (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mp hω
    have hc := bufferWordSuccesses_history e f hef R₀ z₀ ε α g κ H hH root ω hh.1 n
    rw [l.property] at hh
    rw [hh.2] at hc
    simp only [failureWeight,←hc]
  change @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) N.level)) _ _
  rw [he]
  exact measurable_const.indicator N.active_rows
end DirectionalTransience

end

end

end OAI
