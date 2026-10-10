import OAI.Analysis.SeparableQuotients.Positive.SampledSuppression
import OAI.Analysis.SeparableQuotients.Positive.MeasurableCodes

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Sampling
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev ClosedSpan (v : ℕ → V) := Rows.ClosedSpan v
abbrev spanVector (v : ℕ → V) := Rows.spanVector v
abbrev spanCombination (v : ℕ → V) := Rows.spanCombination v
alias spanCombination_coe := Rows.spanCombination_coe
alias denseRange_spanCombination := Rows.denseRange_spanCombination

def SuppressionBoundTwo (v : ℕ → V) : Prop :=
  ∀ (c : ℕ →₀ ℝ) (s : Finset ℕ),
    ‖∑ i ∈ s, c i • v i‖ ≤ 2 * ‖c.sum (fun i a => a • v i)‖

lemma suppressionBoundTwo_of_finite (v : ℕ → V)
    (h : ∀ n (c : Fin n → ℝ) (s : Finset (Fin n)),
      ‖∑ j ∈ s, c j • v j.val‖ ≤ 2 * ‖∑ j, c j • v j.val‖) :
    SuppressionBoundTwo v := by
  intro c s
  obtain ⟨n, hn⟩ := (c.support ∪ s).exists_nat_subset_range
  have hs : s ⊆ Finset.range n := fun i hi => hn (Finset.mem_union_right _ hi)
  have hc : c.support ⊆ Finset.range n := fun i hi => hn (Finset.mem_union_left _ hi)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ s)
  have hsum : (∑ j ∈ t, c j.val • v j.val) = ∑ i ∈ s, c i • v i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro i hi
      exact ⟨⟨i, Finset.mem_range.mp (hs hi)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
    · intros; rfl
  have htotal : (∑ j : Fin n, c j.val • v j.val) = c.sum (fun i a => a • v i) := by
    rw [show (∑ j : Fin n, c j.val • v j.val) =
      ∑ j ∈ Finset.range n, c j • v j from Fin.sum_univ_eq_sum_range (fun j => c j • v j) n]
    exact (Finsupp.sum_of_support_subset c hc (fun i a => a • v i) (by simp)).symm
  simpa only [hsum, htotal] using h n (fun j => c j.val) t

lemma coefficient_bound (v : ℕ → V) (h : SuppressionBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (c : ℕ →₀ ℝ) (i : ℕ) :
    ‖c i‖ ≤ (2 / a) * ‖spanCombination v c‖ := by
  have hh := h c {i}
  simp only [Finset.sum_singleton, norm_smul] at hh
  have hb : ‖c i‖ * a ≤ 2 * ‖spanCombination v c‖ := by
    exact (mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)).trans
      (by simpa only [← spanCombination_coe, Submodule.norm_coe] using hh)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ ha).mpr hb


def suppressedCoord (v : ℕ → V) (i : ℕ) : StrongDual ℝ (ClosedSpan v) :=
  (Finsupp.lapply i).extendOfNorm (spanCombination v)

lemma suppressedCoord_combination (v : ℕ → V) (h : SuppressionBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (c : ℕ →₀ ℝ) (i : ℕ) :
    suppressedCoord v i (spanCombination v c) = c i := by
  apply LinearMap.extendOfNorm_eq (denseRange_spanCombination v)
  exact ⟨2 / a, fun c => coefficient_bound v h ha hv c i⟩

lemma suppressedCoord_bound (v : ℕ → V) (h : SuppressionBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (x : ClosedSpan v) (i : ℕ) :
    ‖suppressedCoord v i x‖ ≤ (2 / a) * ‖x‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le (denseRange_spanCombination v) _
    (fun c => coefficient_bound v h ha hv c i) x

lemma suppressedCoord_ortho (v : ℕ → V) (h : SuppressionBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (i j : ℕ) :
    suppressedCoord v i (spanVector v j) = (Pi.single j (1 : ℝ) : ℕ → ℝ) i := by
  have hc : spanCombination v (Finsupp.single j 1) = spanVector v j := by
    simp [spanCombination, Rows.spanCombination]
  rw [← hc, suppressedCoord_combination v h ha hv]
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]


def suppressedProjection (v : ℕ → V) (s : Finset ℕ) :
    ClosedSpan v →L[ℝ] ClosedSpan v :=
  ∑ i ∈ s, (suppressedCoord v i).smulRight (spanVector v i)

lemma suppressedProjection_apply (v : ℕ → V) (s : Finset ℕ) (x : ClosedSpan v) :
    suppressedProjection v s x = ∑ i ∈ s, suppressedCoord v i x • spanVector v i := by
  simp [suppressedProjection]

lemma suppressedProjection_bound (v : ℕ → V) (h : SuppressionBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (s : Finset ℕ) (x : ClosedSpan v) :
    ‖suppressedProjection v s x‖ ≤ 2 * ‖x‖ := by
  refine (denseRange_spanCombination v).induction_on x (p := fun x =>
    ‖suppressedProjection v s x‖ ≤ 2 * ‖x‖) ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro c
    rw [suppressedProjection_apply]
    simp only [suppressedCoord_combination v h ha hv]
    have hh := h c s
    change ‖((∑ i ∈ s, c i • spanVector v i : ClosedSpan v) : V)‖ ≤
      2 * ‖(spanCombination v c : V)‖
    simpa only [Submodule.coe_sum, Submodule.coe_smul, spanVector, Rows.spanVector,
      spanCombination_coe] using hh

lemma suppressedProjection_combination (v : ℕ → V) (h : SuppressionBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (c : ℕ →₀ ℝ)
    (s : Finset ℕ) (hs : c.support ⊆ s) :
    suppressedProjection v s (spanCombination v c) = spanCombination v c := by
  rw [suppressedProjection_apply]
  simp only [suppressedCoord_combination v h ha hv]
  exact (Finsupp.sum_of_support_subset c hs (fun i a => a • spanVector v i) (by simp)).symm

lemma suppressed_expansion (v : ℕ → V) (h : SuppressionBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (x : ClosedSpan v) :
    HasSum (fun i => suppressedCoord v i x • spanVector v i) x := by
  have hequi : Equicontinuous (fun s : Finset ℕ => (suppressedProjection v s : ClosedSpan v → ClosedSpan v)) := by
    have hb : ∃ C : ℝ, ∀ (s : Finset ℕ) (y : ClosedSpan v),
        ‖suppressedProjection v s y‖ ≤ C * ‖y‖ :=
      ⟨2, fun s y => suppressedProjection_bound v h ha hv s y⟩
    exact ((NormedSpace.equicontinuous_TFAE (suppressedProjection v)).out 4 2).mp hb
  change Tendsto (fun s : Finset ℕ => ∑ i ∈ s, suppressedCoord v i x • spanVector v i)
    atTop (𝓝 x)
  simp only [← suppressedProjection_apply]
  refine (denseRange_spanCombination v).induction_on x (p := fun x =>
    Tendsto (fun s : Finset ℕ => suppressedProjection v s x) atTop (𝓝 x)) ?_ ?_
  · exact hequi.isClosed_setOfPred_tendsto continuous_id
  · intro c
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop c.support] with s hs
    exact (suppressedProjection_combination v h ha hv c s hs).symm



def unconditionalBasisOfSuppression (v : ℕ → V) (h : SuppressionBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) :
    UnconditionalSchauderBasis ℕ ℝ (ClosedSpan v) where
  basis := spanVector v
  coord := suppressedCoord v
  ortho := by
    intro i j
    rw [suppressedCoord_ortho v h ha hv]
    by_cases hij : i = j <;> simp [hij]
  expansion := suppressed_expansion v h ha hv

end SeparableQuotient.Positive.Sampling

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Sampling
open MeasureTheory Filter TopologicalSpace
open scoped Topology
attribute [local instance] dualSubmoduleNormedGroup dualSubmoduleNormedSpace



def IsUnconditionalBasicSequence {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : ℕ → V) : Prop :=
  ∃ b : UnconditionalSchauderBasis ℕ ℝ (ClosedSpan v), ∀ n, (b n : V) = v n




theorem coded_family_unconditional
    {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace I] [DiscreteMeasurableSpace I]
    (μ : Measure I) [IsProbabilityMeasure μ]
    (F : Submodule ℝ (StrongDual ℝ X)) [SeparableSpace F]
    (h : I → StrongDual ℝ (StrongDual ℝ F)) (code : I → ℕ → F)
    (hcode : ∀ a y, Tendsto (fun n => y (code a n)) atTop (𝓝 (h a y)))
    (hnull : ∀ x : UnitBall X, ∀ᵐ a ∂μ, h a (evaluation F x.val) = 0)
    {ε : ℝ} (hε : 0 < ε) (hlower : ∀ a, ε ≤ ‖(h a).comp (evaluation F)‖) :
    ∃ α : ℕ → I, IsUnconditionalBasicSequence (fun n => (h (α n)).comp (evaluation F)) := by
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  let f : I → StrongDual ℝ X := fun a => (h a).comp (evaluation F)
  obtain ⟨α, hα⟩ := exists_sequence_suppression
    (μ := μ) (code := code) (Φ := sequentialCodeValue F)
    (R := evaluationBall F) (f := f)
    (measurable_sequentialCodeValue F)
    (fun a x => sequentialCodeValue_evaluation F (hcode a) x) hnull
  have hs := suppressionBoundTwo_of_finite (fun n => f (α n)) hα
  refine ⟨α, unconditionalBasisOfSuppression (fun n => f (α n)) hs hε
    (fun n => hlower (α n)), ?_⟩
  intro n
  rfl

end SeparableQuotient.Positive.Sampling

end

end

end OAI
