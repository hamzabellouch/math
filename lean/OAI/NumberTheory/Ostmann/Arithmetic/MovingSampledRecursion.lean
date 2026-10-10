import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePrior
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSystem

namespace OAI

/-! # Expanding the sampled giant recursion into its literal histories

This is the recursion of Section 7.4 (7.10)--(7.11), rather than the
whole-atom recursion of Section 4. Each root sample is used by both children.
The child sample trees are independent under the original finite law.
-/

namespace Ostmann
open scoped Classical BigOperators

def MovingSlotData.frequencyTree {σ : Type*} : {n : ℕ} →
    MovingSlotData σ n → FrequencyTree ℤ n
  | _, .leaf s _ => s
  | _, .node s _ _ _ l r => (s, l.frequencyTree, r.frequencyTree)

theorem buildMovingSlotData_frequencyTree {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk a).frequencyTree = t := by
  induction a with
  | leaf => rfl
  | node a l r hl hr =>
      exact Prod.ext rfl (Prod.ext (hl _ _ _) (hr _ _ _))

/-- Discard descendant prime data, keeping all their frequencies. Root
cutoffs may still impose the cross-branch frequency tests of Section 7.4. -/
def movingFrequencySkeleton (σ : Type*) : (n : ℕ) → FrequencyTree ℤ n → MovingSlotData σ n
  | 0, t => .leaf t []
  | n + 1, t => .node t.1 [] [] []
      (movingFrequencySkeleton σ n t.2.1) (movingFrequencySkeleton σ n t.2.2)

def MovingSlotData.rootData {σ : Type*} : {n : ℕ} → MovingSlotData σ n → MovingSlotData σ n
  | _, .leaf s regular => .leaf s regular
  | n + 1, .node s CL CR u l r => .node s CL CR u
      (movingFrequencySkeleton σ n l.frequencyTree) (movingFrequencySkeleton σ n r.frequencyTree)

def movingRootState {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (CL CR u : List σ) (XL XR : ℕ) : MovingSlotState σ :=
  ⟨n + 1, .node t.1 CL CR u
    (movingFrequencySkeleton σ n t.2.1) (movingFrequencySkeleton σ n t.2.2), XL, XR⟩

/-- Original node factors depend on the current prime lists, two giants and
complete frequency tree, not on prime samples which will be made later. -/
noncomputable def movingLocalExtra {σ : Type*}
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) : ℝ :=
  E ⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ s v w

noncomputable def movingSampleRootFactor {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1)) (CL CR u : List σ) (XL XR : ℕ) : ℂ :=
  let x := movingRootState n t CL CR u XL XR
  let sys := movingSlotSystem value childBound pivotBound
  let v := frequencyRoot n t.2.1
  let w := frequencyRoot n t.2.2
  let P := historyPivot sys x t.1 v w
  if ValidTransferNode sys x t.1 v w P then
    (movingSlotCutoff value childBound pivotBound E x t.1 v w : ℂ) else 0

/-- The actual termwise node identity, including failed integer and
divisibility tests. The new giant is the quotient of the composite pivot. -/
theorem movingSample_weight_node {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1))
    (a : TreeLeafTuple (Fin 4 → σ) n) (l r : MovingSampleSlots σ n) (XL XR : ℕ) :
    let u := movingCompensationSlots n a
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let p := historyPivot (movingSlotSystem value childBound pivotBound)
      (movingRootState n t CL CR (flattenMovingSlots n u) XL XR) t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
          MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) (n + 1)
      ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩ t =
        movingSampleRootFactor value childBound pivotBound E n t CL CR (flattenMovingSlots n u) XL XR *
          recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 l, p, XL⟩ t.2.1 *
          star (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 r, p, XR⟩ t.2.2) := by
  dsimp only
  let u := movingCompensationSlots n a
  let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
  let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
  let x : MovingSlotState σ :=
    ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
  let y := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
  let sys := movingSlotSystem value childBound pivotBound
  let P := historyPivot sys y t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
  have hp : historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) = P := rfl
  have hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P ↔
      ValidTransferNode sys y t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P := by
    constructor <;> intro h <;>
      exact ⟨h.root_ne_zero, h.root_unit, h.relation, h.pivot_pos, h.pivot_bound,
        h.left_bound, h.right_bound, h.range_gap, h.pivot_unit⟩
  have hc : movingSlotCutoff value childBound pivotBound (movingLocalExtra E) x t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
      movingSlotCutoff value childBound pivotBound E y t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) := by
    unfold movingSlotCutoff
    have he : movingLocalExtra E x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
        E y t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) := by
      simp only [movingLocalExtra, x, buildMovingSlotData, MovingSlotData.rootData,
        buildMovingSlotData_frequencyTree]
      rfl
    rw [he]
    rfl
  change recursiveTransferWeight sys F _ (n + 1) x t = _
  rw [recursiveTransferWeight]
  simp only [hp]
  rw [hv, hc]
  by_cases h : ValidTransferNode sys y t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
  · simp only [h, ite_true]
    change _ = (if ValidTransferNode sys y t.1 _ _ P then _ else 0) * _ * _
    rw [ite_eq_left h]
    rfl
  · simp only [h, ite_false]
    change 0 = (if ValidTransferNode sys y t.1 _ _ P then _ else 0) * _ * _
    rw [ite_eq_right h, zero_mul, zero_mul]

/-- The finite expansion keeps every internal sample's original prior. -/
noncomputable def movingSampledWeight {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) : ℂ :=
  ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t

theorem movingSampledWeight_node {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound F E (n + 1) t small bulk XL XR =
      ∑ a : TreeLeafTuple (Fin 4 → σ) n,
        let u := movingCompensationSlots n a
        let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
        let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
        let p := historyPivot (movingSlotSystem value childBound pivotBound)
          (movingRootState n t CL CR (flattenMovingSlots n u) XL XR) t.1
            (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
              MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
        (movingCompensationPrior (μ n) n a : ℂ) *
          movingSampleRootFactor value childBound pivotBound E n t CL CR (flattenMovingSlots n u) XL XR *
          movingSampledWeight value μ childBound pivotBound F E n t.2.1
            (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
          star (movingSampledWeight value μ childBound pivotBound F E n t.2.2
            (appendMovingSlotLeaves n u small.2) bulk.2 p XR) := by
  unfold movingSampledWeight
  rw [sum_movingSample_node]
  simp_rw [movingSample_weight_node]
  simp only [movingSamplesPrior, Complex.ofReal_mul, star_sum, star_mul,
    Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

end Ostmann

end OAI
