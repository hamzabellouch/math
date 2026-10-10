import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferRestorationScript
import OAI.Probability.Ballisticity.Geometry.BufferStructuralHeight

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

structure AdaptedBufferNode {d : ℕ} (e : Direction d) where
  level : ℝ
  radius : ℝ
  law : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) level)
  law_rows : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) level)) _ law
  active : Set (Environment d)
  active_rows : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) level)] active

noncomputable def bufferNextRadius (R₀ r ε α : ℝ) (b : Bool) : ℝ :=
  max R₀ ((if b then 1+α else 1-ε)*r)

noncomputable def bufferRestoreLength (R₀ r ε α : ℝ) (b : Bool) : ℕ :=
  ⌈max 0 (R₀-((if b then 1+α else 1-ε)*r))⌉₊

lemma bufferRestoreLength_enough (R₀ r ε α : ℝ) (b : Bool) :
    bufferNextRadius R₀ r ε α b ≤
      (if b then 1+α else 1-ε)*r + bufferRestoreLength R₀ r ε α b := by
  have h := Nat.le_ceil (max 0 (R₀-((if b then 1+α else 1-ε)*r)))
  unfold bufferNextRadius bufferRestoreLength
  apply max_le
  · have := le_max_right 0 (R₀-((if b then 1+α else 1-ε)*r))
    linarith
  · exact le_add_of_nonneg_right (Nat.cast_nonneg _)

lemma bufferStage_branch_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {H : ℕ} (hH : 0 < H) (k : ℕ) (b : Bool) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+k))]
      {ω | bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k ∧
        (BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω ↔ b=true)} := by
  have hstop := bufferFirstFailure_eq_measurable (realPosition (step e)) f a (z₀+(1-ε)*r) g π hπ H k
  have hpass := bufferStage_success_stopped_rows e f a z₀ r ε α g π hπ hH k
  cases b
  · convert hstop.diff hpass using 1
    ext ω
    simp only [Bool.false_eq_true,iff_false,Set.mem_sdiff,Set.mem_ofPred_eq]
    tauto
  · convert hpass using 1
    ext ω
    simp

noncomputable def restoredStoppedLaw {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k m : ℕ) (ω : Environment d) :
    SupportedPairMeasures (PairAtHeight (realPosition (step e)) (a+k+1)) :=
  ⟨(bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k ω).val.map (pairRestore e f m), by
    apply ae_iff.mp
    rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
    filter_upwards [ae_iff.mpr (bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k ω).property] with x hx
    exact pairRestore_height e f hef m (a+k) x hx⟩

lemma restoredStoppedLaw_rows {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k m : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k+1))) _
      (restoredStoppedLaw e f hef a z₀ r ε α g π H hH κ k m) := by
  apply Measurable.subtype_mk
  have hm := (bufferStageStoppedProbability_rows e f a z₀ r ε α g π hπ H hH κ k).subtype_val
  have hu : rowSigma (BelowHeight (realPosition (step e)) (a+k)) ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+k+1)) :=
    by simpa only [Nat.cast_one] using rowSigma_below_height_mono (realPosition (step e)) (a+k) 1
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.map_apply (measurable_of_countable _) hU]
  exact ((Measure.measurable_coe ((measurable_of_countable _) hU)).comp hm).mono hu le_rfl

noncomputable def bufferChildNode {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (N : AdaptedBufferNode e)
    (H : ℕ) (hH : 0 < H) (k : ℕ) (b : Bool) : AdaptedBufferNode e where
  level := N.level+k+1
  radius := bufferNextRadius R₀ N.radius ε α b
  law := restoredStoppedLaw e f hef N.level z₀ N.radius ε α g N.law H hH κ k
    (bufferRestoreLength R₀ N.radius ε α b)
  law_rows := restoredStoppedLaw_rows e f hef N.level z₀ N.radius ε α g N.law N.law_rows H hH κ k _
  active := N.active ∩ {ω | bufferFirstFailure (realPosition (step e)) f N.level (z₀+(1-ε)*N.radius) g N.law H ω = k ∧
    (BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω ↔ b=true)}
  active_rows := by
    have ha := N.active_rows
    have hb := bufferStage_branch_rows e f N.level z₀ N.radius ε α g N.law N.law_rows hH k b
    have h1 := rowSigma_below_height_mono (realPosition (step e)) N.level k
    have h2 : rowSigma (BelowHeight (realPosition (step e)) (N.level+k)) ≤
        rowSigma (BelowHeight (realPosition (step e)) (N.level+k+1)) := by
      simpa only [Nat.cast_one] using rowSigma_below_height_mono (realPosition (step e)) (N.level+k) 1
    exact (h2 _ (h1 _ ha)).inter (h2 _ hb)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def BufferNodeValid {d : ℕ} (e f : Direction d) (z₀ : ℝ) (κ : ℝ≥0) (N : AdaptedBufferNode e) : Prop :=
  ∀ ω : Environment d, (∀ y u, κ ≤ (ω y).1 u) → ω ∈ N.active →
    IsProbabilityMeasure (N.law ω).val ∧
      ∀ᵐ x ∂(N.law ω).val, z₀+N.radius ≤ signedCoordinate f (x.2-x.1)

lemma bufferChildNode_valid {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) {κ : ℝ≥0} (hκpos : 0 < κ) (hκ1 : κ ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 ≤ ε) (N : AdaptedBufferNode e)
    (hr : 0 ≤ N.radius) (hN : BufferNodeValid e f z₀ κ N)
    (H : ℕ) (hH : 0 < H) (k : ℕ) (b : Bool) :
    BufferNodeValid e f z₀ κ (bufferChildNode e f hef R₀ z₀ ε α g κ N H hH k b) := by
  intro ω hκ hω
  have hparent : ω ∈ N.active := hω.1
  have hk : bufferFirstFailure (realPosition (step e)) f N.level (z₀+(1-ε)*N.radius) g N.law H ω = k := hω.2.1
  have hb : BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω ↔ b=true := hω.2.2
  obtain ⟨hp,hgap⟩ := hN ω hκ hparent
  let := hp
  have hp' : IsProbabilityMeasure (bufferStageStoppedProbability e f N.level z₀ N.radius ε α g N.law H hH κ k ω).val := by
    simp only [bufferStageStoppedProbability,ite_eq_left hk]
    exact bufferStageRetainedLaw_probability e f N.level z₀ N.radius ε α g N.law hH ω
      (fun y => hκ y e) hκpos hκ1 hg hg1 hr hε hgap
  let := hp'
  have hmap : IsProbabilityMeasure ((bufferStageStoppedProbability e f N.level z₀ N.radius ε α g N.law H hH κ k ω).val.map
      (pairRestore e f (bufferRestoreLength R₀ N.radius ε α b))) := by
    infer_instance
  have hgapmap : ∀ᵐ x ∂(bufferStageStoppedProbability e f N.level z₀ N.radius ε α g N.law H hH κ k ω).val.map
      (pairRestore e f (bufferRestoreLength R₀ N.radius ε α b)),
      z₀+bufferNextRadius R₀ N.radius ε α b ≤ signedCoordinate f (x.2-x.1) := by
    rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurableSet_le measurable_const (measurable_of_countable _))]
    filter_upwards [bufferStageStoppedProbability_gap e f N.level z₀ N.radius ε α g N.law H hH κ k ω] with x hx
    rw [pairRestore_gap]
    have hR := bufferRestoreLength_enough R₀ N.radius ε α b
    cases b
    · have hn : ¬ BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω := by simpa using hb
      simp only [ite_eq_right hn] at hx
      simp only [Bool.false_eq_true,↓reduceIte] at hR
      linarith
    · have hy : BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω := hb.mpr rfl
      simp only [ite_eq_left hy] at hx
      simp only [↓reduceIte] at hR
      linarith
  exact ⟨hmap,hgapmap⟩

lemma bufferChildNode_cover {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (N : AdaptedBufferNode e)
    (H : ℕ) (hH : 0 < H) :
    (⋃ p : ℕ × Bool, (bufferChildNode e f hef R₀ z₀ ε α g κ N H hH p.1 p.2).active) = N.active := by
  ext ω
  constructor
  · rintro ⟨_,⟨p,rfl⟩,hω⟩
    exact hω.1
  · intro hω
    let k := bufferFirstFailure (realPosition (step e)) f N.level (z₀+(1-ε)*N.radius) g N.law H ω
    let b := decide (BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω)
    apply Set.mem_iUnion.mpr
    refine ⟨(k,b),hω,rfl,?_⟩
    simp [b]

lemma bufferChildNode_disjoint {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (N : AdaptedBufferNode e)
    (H : ℕ) (hH : 0 < H) :
    Pairwise (Disjoint on fun p : ℕ × Bool =>
      (bufferChildNode e f hef R₀ z₀ ε α g κ N H hH p.1 p.2).active) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro ω hp hq
  apply hpq
  apply Prod.ext
  · exact hp.2.1.symm.trans hq.2.1
  · have hh : (p.2=true) ↔ (q.2=true) := hp.2.2.symm.trans hq.2.2
    exact Bool.eq_iff_iff.mpr hh
end DirectionalTransience

end

end

end OAI
