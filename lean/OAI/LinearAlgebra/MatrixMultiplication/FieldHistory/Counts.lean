import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Schedule
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ShapeEncoding

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def shapeCounts {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) : ℕ :=
  ∑ i, if code i = u then weight i else 0

theorem shapeCounts_sum {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) : ∑ u, shapeCounts code weight u = ∑ i, weight i := by
  unfold shapeCounts
  rw [Finset.sum_comm]
  simp

theorem shapeCounts_positive {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) (hu : 0 < shapeCounts code weight u) :
    ∃ i, code i = u ∧ 0 < weight i := by
  by_contra hn
  have hz : shapeCounts code weight u = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    split_ifs with heq
    · by_contra hne
      exact hn ⟨i, heq, Nat.pos_of_ne_zero hne⟩
    · rfl
  omega

theorem shapeCounts_at {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (hi : Function.Injective code) (i : I) :
    shapeCounts code weight (code i) = weight i := by
  unfold shapeCounts
  simp only [hi.eq_iff]
  simp

theorem Work.parentShape_spec {K : ℕ} (w : Work K) :
    ShapeBounded w.parentShape ∧ shapeTotal w.parentShape = 4 * w.halfLength := by
  cases w with
  | stageA h => exact positiveInitial_shape_spec _ h.property
  | stageB h => exact positiveSecond_shape_spec _ h.property
  | stageC h =>
      exact ⟨mem_shapes_bounded (bShape_size h.1.val) (by omega),
        mem_shapes_total (bShape_size h.1.val)⟩

theorem Work.splitShape_spec {K : ℕ} (w : Work K) (b : w.Branch) :
    ShapeBounded (w.splitShape b) ∧ shapeTotal (w.splitShape b) = 2 * w.halfLength := by
  cases w with
  | stageA h => exact stageA_shape_spec _ _ h.property (aSplit_mem ⟨h, b, false⟩)
  | stageB h => exact stageB_shape_spec _ _ h.property (bSplit_mem ⟨h, b, false⟩)
  | stageC h => exact stageC_shape_spec _ (bShape_size h.1.val) h.1.property b

theorem Work.splitShape_le {K : ℕ} (w : Work K) (b : w.Branch) :
    ∀ i, w.splitShape b i ≤ w.parentShape i := by
  cases w with
  | stageA h => exact below_le (aSplit_mem ⟨h, b, false⟩)
  | stageB h => exact below_le (bSplit_mem ⟨h, b, false⟩)
  | stageC h => exact below_le (stageCAtom_mem _ (bShape_size h.1.val) h.1.property b)

theorem Work.splitShape_injective {K : ℕ} (w : Work K) :
    Function.Injective w.splitShape := by
  cases w with
  | stageA h => exact stageA_get_injective _ h.property
  | stageB h => exact stageB_get_injective _ h.property
  | stageC h => exact stageCAtom_injective _ (bShape_size h.1.val) h.1.property

def branchShape {K : ℕ} (w : PlacedWork K) (b : w.1.Branch) : JointPopulation.Shape :=
  encodePhysicalShape w.2 (w.1.splitShape b) (w.1.splitShape_spec b).1

theorem branchShape_injective {K : ℕ} (w : PlacedWork K) :
    Function.Injective (branchShape w) := by
  intro a b hab
  exact w.1.splitShape_injective (encodePhysicalShape_inj w.2 hab)

def jointCounts {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : JointPopulation.Shape → ℕ :=
  shapeCounts (branchShape w) (branchPopulation allocation dilation w)

def activeCounts {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) : JointPopulation.Shape → ℕ := jointCounts allocation dilation h.val

def activeParentShape {K tick : ℕ} (h : Active K tick) : Shape :=
  physicalShape h.val.2 h.val.1.parentShape

def activeHalfLength {K tick : ℕ} (h : Active K tick) : ℕ := h.val.1.halfLength

theorem jointCounts_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : ∑ u, jointCounts allocation dilation w u =
      population allocation dilation (w.1.source, w.2) := by
  rw [jointCounts, shapeCounts_sum, branchPopulation_sum]

theorem jointCounts_at {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    jointCounts allocation dilation w (branchShape w b) =
      branchPopulation allocation dilation w b :=
  shapeCounts_at _ _ (branchShape_injective w) b

theorem jointCounts_support_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) :
    u.1.val + u.2.1.val + u.2.2.val = 2 * w.1.halfLength := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  exact (encodePhysicalShape_total _ _ _).trans (w.1.splitShape_spec b).2

theorem jointCounts_support_le {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) (s : Fin 3) :
    (JointPopulation.shapeSide s u).val ≤ physicalShape w.2 w.1.parentShape s := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  rw [branchShape, encodePhysicalShape_side]
  exact w.1.splitShape_le b (w.2.symm s)

def shapePositionMap {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (Σ b : w.1.Branch, Fin (branchPopulation allocation dilation w b)) →
      (Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) :=
  fun p => ⟨branchShape w p.1,
    ⟨p.2.val, by rw [jointCounts_at]; exact p.2.isLt⟩⟩

theorem shapePositionMap_injective {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : Function.Injective (shapePositionMap allocation dilation w) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ heq
  have hbc : b = c := branchShape_injective w (congrArg Sigma.fst heq)
  subst c
  have hij : i.val = j.val := congrArg (fun p => p.2.val) heq
  have : i = j := Fin.ext hij
  subst j
  rfl

theorem shapePositionMap_surjective {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : Function.Surjective (shapePositionMap allocation dilation w) := by
  rintro ⟨u, i⟩
  obtain ⟨b, heq, hb⟩ := shapeCounts_positive _ _ u (Nat.zero_lt_of_lt i.isLt)
  subst u
  refine ⟨⟨b, ⟨i.val, ?_⟩⟩, ?_⟩
  · simpa only [jointCounts_at] using i.isLt
  · rfl

def branchPositionEquiv {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) ≃
      (Σ b : w.1.Branch, Fin (branchPopulation allocation dilation w b)) :=
  (Equiv.ofBijective (shapePositionMap allocation dilation w)
    ⟨shapePositionMap_injective allocation dilation w,
      shapePositionMap_surjective allocation dilation w⟩).symm

@[simp] theorem branchPositionEquiv_shape {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K)
    (p : Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) :
    branchShape w (branchPositionEquiv allocation dilation w p).1 = p.1 := by
  exact congrArg Sigma.fst ((branchPositionEquiv allocation dilation w).symm_apply_apply p)

def rootShape {K : ℕ} (h : Initial K) (phi : Placement) : JointPopulation.Shape :=
  encodePhysicalShape phi (initialShape h) (root_shape_spec _ (initialShape_mem h)).1

def initialJointCounts {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) : JointPopulation.Shape → ℕ :=
  shapeCounts (fun p : Fin sortedInitial.length × Placement => rootShape (j, p.1) p.2)
    (fun p => population allocation dilation (.initial (j, p.1), p.2))

theorem initialJointCounts_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) : ∑ u, initialJointCounts allocation dilation j u =
      populationLength (K := K) allocation dilation := by
  rw [initialJointCounts, shapeCounts_sum, Fintype.sum_prod_type]
  exact initial_population_sum allocation dilation j

theorem initialJointCounts_support {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape)
    (hu : 0 < initialJointCounts allocation dilation j u) :
    u.1.val + u.2.1.val + u.2.2.val = 16 := by
  obtain ⟨p, rfl, _⟩ := shapeCounts_positive _ _ u hu
  exact (encodePhysicalShape_total _ _ _).trans (root_shape_spec _ (initialShape_mem _)).2

end MatrixMultiplication.AllFieldHistory

end

end OAI
