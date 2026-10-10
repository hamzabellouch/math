import OAI.Probability.DilutedSpin.FullCubeConditionalContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
noncomputable local instance projectionShiftAveragePropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_add_eq (D : (α → Fin L) → Prop) (F G : (α → Fin L) → ℝ) :
    average D (fun Q => F Q+G Q)=average D F+average D G := by
  unfold average
  rw [← FiniteLaw.expect_add]
  apply FiniteLaw.expect_congr
  intro Q
  split_ifs <;> ring

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance projectionShiftErrorPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]

 
noncomputable def projectionShiftError (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (Q : α → Fin L) : ℝ :=
  2*Real.sqrt (projectorChangeSq T
    (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
    (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f))

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_nonneg (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (Q : α → Fin L) :
    0≤projectionShiftError a C e T f Q := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_sq (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (Q : α → Fin L) :
    (projectionShiftError a C e T f Q)^2=4*projectorChangeSq T
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
      (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f) := by
  unfold projectionShiftError
  rw [mul_pow,Real.sq_sqrt (projectorChangeSq_nonneg T _ _)]
  norm_num

/-- Literal normalized regular-assignment estimate (projection-shift-error).
Constants depend ONLY on the reduced child topologies, not on kernels,
spatial dimension, depth count, target histories, or extension choices. -/
theorem averaged_projectionShiftError_sq_le (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => (projectionShiftError a C e T f Q)^2) ≤
      8*((Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)+(Fintype.card ι:ℝ)^2)/(L:ℝ) := by
  have hsum := add_le_add
    (averaged_fullCube_schedule_le a C e he η hlarge D hD T f hf)
    (averaged_fullCube_evaluation_le a C e D (fun Q hQ j v =>
      admissible_lower (C j) _ (hD Q hQ j).1 v) T f hf)
  simp_rw [← Finset.sum_div] at hsum
  have htriangle : DepthAverage.average D (fun Q =>
      projectorChangeSq T
        (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
        (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f)) ≤
      2*(DepthAverage.average D (fun Q => projectorChangeSq T
        (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
        (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val) T f))+
        DepthAverage.average D (fun Q => projectorChangeSq T
        (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val) T f)
        (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f))) := by
    rw [← DepthAverage.average_add_eq,← DepthAverage.average_mul_left]
    apply DepthAverage.average_mono_on
    intro Q _
    exact projectorChangeSq_triangle T _ _ _
  simp_rw [projectionShiftError_sq]
  rw [DepthAverage.average_mul_left]
  exact (mul_le_mul_of_nonneg_left
    (htriangle.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))) (by norm_num)).trans_eq (by ring)

omit [Fintype α] [DecidableEq α] [NeZero L] in
/-- Every actual target history has contraction error at most this SAME h_N.
No regularity or independence assumption on its union with the old tree. -/
theorem target_contraction_shift_le (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (Q : α → Fin L) (Target : PrescribedTree L) (u v : Target.Leaf) :
    PrescribedTree.targetContractionChangeSq Target T u v
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
      (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f) ≤
        (projectionShiftError a C e T f Q)^2 := by
  rw [projectionShiftError_sq]
  exact PrescribedTree.targetContractionChangeSq_le Target T u v _ _
    (conditionalScheduledProduct_bound L 0 _ C _ T f hf)
    (conditionalScheduledProduct_bound L 0 _ C _ T f hf)

omit [Fintype α] [DecidableEq α] [NeZero L] in
/-- The universal shift error is valid in the literal matrix projection
error, before taking signed histories or any physical-root expectation. -/
theorem matrixProjectionError_shift_le {I : Type} [Fintype I] [DecidableEq I]
    (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (Q : α → Fin L) (Target : PrescribedTree L) (q : I → Target.Leaf) (u v : I)
    (A : (I → FinitePath Ω L) → ℝ) :
    PrescribedTree.matrixProjectionError Target q T u v A
      (conditionalScheduledProduct L 0 (Q a).val C (fun j w => (Q (e j w)).val) T f) ≤
    PrescribedTree.matrixProjectionError Target q T u v A
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j w => (Q (e j w)).val+1) T f)+
      projectionShiftError a C e T f Q := by
  have h := PrescribedTree.matrixProjectionError_change_spatial Target q T u v A
    (conditionalScheduledProduct L 0 (Q a).val C (fun j w => (Q (e j w)).val) T f)
    (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j w => (Q (e j w)).val+1) T f)
    (conditionalScheduledProduct_bound L 0 _ C _ T f hf)
    (conditionalScheduledProduct_bound L 0 _ C _ T f hf)
  exact h

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
