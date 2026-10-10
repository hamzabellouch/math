import OAI.GroupTheory.PolycyclicRecognition.Analysis.CenteredImagePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectPrefixTuples

namespace OAI

/-! # Centering every transition of the actual image tuple -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {X G : Type*} [Group G]

def centeredVertexTuple (f : X → G) (v : ℕ → X) (h : ℕ) : Fin h → G :=
  fun i => (f (v 0))⁻¹ * f (v (i.val + 1))

theorem basedTuplePosition_centeredVertexTuple
    (f : X → G) (v : ℕ → X) (h : ℕ) {j : ℕ} (hj : j ≤ h) :
    basedTuplePosition (centeredVertexTuple f v h) j = (f (v 0))⁻¹ * f (v j) := by
  cases j with
  | zero => simp only [basedTuplePosition_zero, inv_mul_cancel]
  | succ j =>
    have hj' : j < h := by omega
    simpa only [centeredVertexTuple, Nat.add_sub_cancel] using
      basedTuplePosition_succ (centeredVertexTuple f v h) ⟨j, hj'⟩

theorem centeredVertexTuple_transition (f : X → G) (v : ℕ → X) {h : ℕ} (j : Fin h) :
    (basedTuplePosition (centeredVertexTuple f v h) j.val)⁻¹ *
        basedTuplePosition (centeredVertexTuple f v h) (j.val + 1) =
      (f (v j.val))⁻¹ * f (v (j.val + 1)) := by
  rw [basedTuplePosition_centeredVertexTuple f v h j.isLt.le,
    basedTuplePosition_centeredVertexTuple f v h j.isLt]
  group

variable [TopologicalSpace X] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The common centering cancels between successive coordinates, including
the first transition from the identity. -/
def centeredTuplePath (f : X → G) (hf : Continuous f) (v : ℕ → X) {h : ℕ}
    (path : ∀ j : Fin h, Path (v j.val) (v (j.val + 1))) (j : Fin h) :
    Path (1 : G) ((basedTuplePosition (centeredVertexTuple f v h) j.val)⁻¹ *
      basedTuplePosition (centeredVertexTuple f v h) (j.val + 1)) :=
  (centeredImagePath f hf (path j)).cast rfl (centeredVertexTuple_transition f v j)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem centeredTuplePath_height_bound
    (f : X → G) (hf : Continuous f) (v : ℕ → X) {h : ℕ}
    (path : ∀ j : Fin h, Path (v j.val) (v (j.val + 1)))
    (π : G →* Multiplicative W) (E : Fin h → Set W) (r B : ℝ)
    (hheight : ∀ j t, ∃ w ∈ E j,
      ‖(π (f (path j t))).toAdd - (π (f (v j.val))).toAdd - r • w‖ ≤ B) :
    ∀ j t, ∃ w ∈ E j, ‖(π (centeredTuplePath f hf v path j t)).toAdd - r • w‖ ≤ B := by
  intro j t
  obtain ⟨w, hw, he⟩ := hheight j t
  refine ⟨w, hw, ?_⟩
  change ‖(π ((f (v j.val))⁻¹ * f (path j t))).toAdd - r • w‖ ≤ B
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
  simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he

end PolycyclicRecognition

namespace PolycyclicRecognition

open scoped NNReal

variable {X G : Type*} [PseudoMetricSpace X] [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

theorem centeredTuplePath_metric_bound
    (f : X → G) {K : ℝ≥0} (hf : LipschitzWith K f) (v : ℕ → X) {h : ℕ}
    (path : ∀ j : Fin h, Path (v j.val) (v (j.val + 1))) (L κ : ℝ)
    (hmetric : ∀ j, PathMetricBound (path j) L κ) :
    ∀ j, PathMetricBound (centeredTuplePath f hf.continuous v path j) (K * L) (K * κ) :=
  fun j => centeredImagePath_metric_bound f hf (path j) (hmetric j)

end PolycyclicRecognition

end

end OAI
