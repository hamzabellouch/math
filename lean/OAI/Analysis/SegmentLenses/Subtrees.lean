import OAI.Analysis.SegmentLenses.Canonical

namespace OAI

/-!
# Subtree projections and exact weighted radii
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


namespace SegmentEmbedding
variable {V W : Type*} [DecidableEq V] [DecidableEq W] [SegmentSystem V] [SegmentSystem W]




theorem primal_range_coordinateClosure (e : SegmentEmbedding (V := V) (W := W)) :
    e.primalIsometry.range =
      (Submodule.span ℝ (Set.range (fun v => unitVector (e.toEmbedding v)))).topologicalClosure := by
  let S := Submodule.span ℝ (Set.range (fun v => unitVector (e.toEmbedding v)))
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    change e.primalMap x ∈ S.topologicalClosure
    refine UniformSpace.Completion.induction_on x
      (S.isClosed_topologicalClosure.preimage e.primalMap.continuous) ?_
    intro u
    rw [test_as_sum u]
    simp only [map_sum,map_smul]
    apply S.topologicalClosure.sum_mem
    intro v hv
    rw [e.primalMap_unitVector]
    exact S.topologicalClosure.smul_mem _
      (S.le_topologicalClosure (Submodule.subset_span ⟨v,rfl⟩))
  · apply S.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      exact ⟨unitVector v,e.primalMap_unitVector v⟩
    · exact e.primalIsometry.isometry.isClosedEmbedding.isClosed_range



def primalProjection (e : SegmentEmbedding (V := V) (W := W)) : Primal W →L[ℝ] Primal W :=
  e.primalMap.comp e.primalRestriction

@[simp] theorem primalProjection_apply (e : SegmentEmbedding (V := V) (W := W)) (x : Primal W) :
    e.primalProjection x = e.primalMap (e.primalRestriction x) := rfl

theorem norm_primalProjection_le (e : SegmentEmbedding (V := V) (W := W)) (x : Primal W) :
    ‖e.primalProjection x‖ ≤ ‖x‖ := by
  rw [e.primalProjection_apply,e.norm_primalMap]
  exact e.norm_primalRestriction_le x

@[simp] theorem primalProjection_idempotent (e : SegmentEmbedding (V := V) (W := W)) (x : Primal W) :
    e.primalProjection (e.primalProjection x) = e.primalProjection x := by
  simp only [e.primalProjection_apply,e.primalRestriction_primalMap]

@[simp] theorem primalProjection_unitVector (e : SegmentEmbedding (V := V) (W := W)) (v : V) :
    e.primalProjection (unitVector (e.toEmbedding v)) = unitVector (e.toEmbedding v) := by
  rw [← e.primalMap_unitVector,e.primalProjection_apply,e.primalRestriction_primalMap]

@[simp] theorem primalProjection_unitVector_outside (e : SegmentEmbedding (V := V) (W := W))
    (w : W) (hw : w ∉ Set.range e.toEmbedding) : e.primalProjection (unitVector w) = 0 := by
  have hr : e.testRestriction (Test.ofFinsupp (Finsupp.single w 1)) = 0 := by
    apply Finsupp.ext
    intro v
    change (Finsupp.single w (1:ℝ)) (e.toEmbedding v) = 0
    have hn : w ≠ e.toEmbedding v := fun he => hw ⟨v,he.symm⟩
    simp [hn]
  rw [e.primalProjection_apply,unitVector,e.primalRestriction_test,hr]
  simp


def dualRestriction (e : SegmentEmbedding (V := V) (W := W)) (z : FullDual W) : FullDual V :=
  z.comp e.primalMap



def dualProjection (e : SegmentEmbedding (V := V) (W := W)) (z : FullDual W) : FullDual W :=
  z.comp e.primalProjection

theorem norm_dualProjection_le (e : SegmentEmbedding (V := V) (W := W)) (z : FullDual W) :
    ‖e.dualProjection z‖ ≤ ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖z (e.primalProjection x)‖ ≤ _
  exact (z.le_opNorm _).trans (mul_le_mul_of_nonneg_left (e.norm_primalProjection_le x) (norm_nonneg _))



theorem norm_dualRestriction_eq (e : SegmentEmbedding (V := V) (W := W)) (z : FullDual W) :
    ‖e.dualRestriction z‖ = ‖e.dualProjection z‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have he : e.dualRestriction z x = e.dualProjection z (e.primalMap x) := by
      change z (e.primalMap x) = z (e.primalMap (e.primalRestriction (e.primalMap x)))
      rw [e.primalRestriction_primalMap]
    rw [he]
    exact ((e.dualProjection z).le_opNorm _).trans_eq (by rw [e.norm_primalMap])
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖(e.dualRestriction z) (e.primalRestriction x)‖ ≤ _
    exact ((e.dualRestriction z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (e.norm_primalRestriction_le x) (norm_nonneg _))

@[simp] theorem dualProjection_coordinate (e : SegmentEmbedding (V := V) (W := W))
    (z : FullDual W) (v : V) : e.dualProjection z (unitVector (e.toEmbedding v)) = z (unitVector (e.toEmbedding v)) := by
  change z (e.primalProjection (unitVector _)) = _
  rw [e.primalProjection_unitVector]

@[simp] theorem dualProjection_coordinate_outside (e : SegmentEmbedding (V := V) (W := W))
    (z : FullDual W) (w : W) (hw : w ∉ Set.range e.toEmbedding) : e.dualProjection z (unitVector w) = 0 := by
  change z (e.primalProjection (unitVector w)) = 0
  rw [e.primalProjection_unitVector_outside w hw,map_zero]

end SegmentEmbedding



section ExactWeightedStatement
variable {V I : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V] [Fintype I]



theorem weighted_stability {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (w : FiniteLaw I) (hw : ∀ i, 0 < w.weight i) (z : I → FullDual V)
    (hz : ∀ i, ‖z i‖ ≤ 1) (p : Test V) (hp : ‖p‖ ≤ 1)
    (hpH : p.coeff.support ⊆ H) :
    let δ := 1-(w.expect z) (p : Primal V)
    let δi := fun i => 1-z i (p : Primal V)
    let η := ‖tail H (w.expect z)‖
    δ = w.mean δi ∧ 0 ≤ δ ∧ ∀ i,
      0 ≤ δi i ∧ δi i ≤ δ / w.weight i ∧
      ‖tail H (z i)‖ ≤ (w.weight i)⁻¹ * Real.sqrt ((η+Real.sqrt (2*δ))^2+4*δ) +
        Real.sqrt (2*δi i) := by
  dsimp only
  have hd := weighted_deficits (H := H) w hw z hz p hp
  refine ⟨hd.2.1,?_,fun i => ⟨hd.1 i,hd.2.2 i,weighted_tail_bound hH w hw z hz p hp hpH i⟩⟩
  rw [hd.2.1]
  exact w.mean_nonneg hd.1

end ExactWeightedStatement

section ExactObstructionRadii
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

private theorem safety_radius_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < a/(2*b) ∧ a/(2*b) ≤ a/b := by
  have hb : 0 < b := ha.trans_le hab
  constructor
  · positivity
  · apply div_le_div_of_nonneg_left ha.le hb
    linarith


theorem infinite_obstruction_radii (e : BInfinite ≃L[ℝ] D) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hlower : ∀ x : BInfinite, a*‖x‖ ≤ ‖e x‖)
    (hupper : ∀ x : BInfinite, ‖e x‖ ≤ b*‖x‖) :
    oneSidedModulus D (a/b) = 0 ∧ oneSidedModulus D (a/(2*b)) = 0 := by
  have hs := safety_radius_le ha hab
  exact ⟨infinite_equivalent_modulus_zero e ha hab hlower hupper
    (div_pos ha (ha.trans_le hab)) le_rfl,
    infinite_equivalent_modulus_zero e ha hab hlower hupper hs.1 hs.2⟩


theorem forest_obstruction_radii (e : X ≃L[ℝ] D) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hlower : ∀ x : X, a*‖x‖ ≤ ‖e x‖) (hupper : ∀ x : X, ‖e x‖ ≤ b*‖x‖) :
    oneSidedModulus D (a/b) = 0 ∧ oneSidedModulus D (a/(2*b)) = 0 := by
  have hs := safety_radius_le ha hab
  exact ⟨forest_equivalent_modulus_zero e ha hab hlower hupper
    (div_pos ha (ha.trans_le hab)) le_rfl,
    forest_equivalent_modulus_zero e ha hab hlower hupper hs.1 hs.2⟩

end ExactObstructionRadii

namespace IndexedForest
variable {I : Type*} [DecidableEq I] {height : I → ℕ}


theorem unbounded_obstruction_radii (hunbounded : ∀ n : ℕ, ∃ i : I, n ≤ height i)
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (e : X height ≃L[ℝ] D)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlower : ∀ x : X height, a*‖x‖ ≤ ‖e x‖) (hupper : ∀ x : X height, ‖e x‖ ≤ b*‖x‖) :
    oneSidedModulus D (a/b) = 0 ∧ oneSidedModulus D (a/(2*b)) = 0 := by
  have hs := safety_radius_le ha hab
  exact ⟨unbounded_equivalent_modulus_zero hunbounded e ha hab hlower hupper
    (div_pos ha (ha.trans_le hab)) le_rfl,
    unbounded_equivalent_modulus_zero hunbounded e ha hab hlower hupper hs.1 hs.2⟩

end IndexedForest




end SegmentLenses


end

end OAI
