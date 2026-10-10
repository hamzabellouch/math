import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

abbrev TreeVertex (d : ℕ) :=
  {word : List (Fin d) // List.IsChain (fun first second : Fin d => first ≠ second) word}

def treeAdj {d : ℕ} (u v : TreeVertex d) : Prop :=
  (∃ c : Fin d, v.1 = u.1 ++ [c]) ∨
  (∃ c : Fin d, u.1 = v.1 ++ [c])

structure TreeAut (d : ℕ) where
  toEquiv : TreeVertex d ≃ TreeVertex d
  map_adj : ∀ u v, treeAdj (toEquiv u) (toEquiv v) ↔ treeAdj u v

def relabel {d : ℕ} {α : Type*} (g : TreeAut d)
    (x : TreeVertex d → α) : TreeVertex d → α :=
  fun v => x (g.toEquiv.symm v)

inductive IsingSpin where
  | neg
  | pos
  deriving DecidableEq

protected abbrev IsingSpin.enumList : List IsingSpin := [.neg, .pos]

protected theorem IsingSpin.enumList_getElem?_ctorIdx_eq (x : IsingSpin) :
    IsingSpin.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem IsingSpin.enumList_nodup : IsingSpin.enumList.Nodup := by decide

instance : Fintype IsingSpin where
  elems := ⟨IsingSpin.enumList, IsingSpin.enumList_nodup⟩
  complete x := by cases x <;> decide

instance isingSpinMeasurable : MeasurableSpace IsingSpin := ⊤

def uniform01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

instance uniform01Probability : IsProbabilityMeasure uniform01 where
  measure_univ := by simp [uniform01]

def labelMeasure (d : ℕ) : Measure (TreeVertex d → ℝ) := by
  classical
  exact Measure.infinitePi (fun _ : TreeVertex d => uniform01)

def ConnectedFinset {d : ℕ} (D : Finset (TreeVertex d)) : Prop :=
  D.Nonempty ∧
    ∀ u ∈ D, ∀ v ∈ D,
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ D ∧ y ∈ D ∧ treeAdj x y) u v

def inducedEdges {d : ℕ} (D : Finset (TreeVertex d)) :
    Finset (TreeVertex d × TreeVertex d) := by
  classical
  exact (D.product D).filter (fun e =>
    treeAdj e.1 e.2 ∧ e.1.1.length < e.2.1.length)

def freeCylinderWeight {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ENNReal :=
  ENNReal.ofReal
    ((1 / 2 : ℝ) *
      Finset.prod (inducedEdges D) (fun e =>
        (1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

def HasFreeIsingLaw {d : ℕ} (theta : ℝ)
    (mu : Measure (TreeVertex d → IsingSpin)) : Prop :=
  ∀ (D : Finset (TreeVertex d)), ConnectedFinset D →
    ∀ eta : TreeVertex d → IsingSpin,
      mu {x | ∀ v ∈ D, x v = eta v} = freeCylinderWeight theta D eta

def IsFactorOfIID (d : ℕ) (theta : ℝ) : Prop :=
  ∃ Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin),
    Measurable Phi ∧
    HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)) ∧
    ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U)

theorem free_ising_factor_iff_threshold :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta → (IsFactorOfIID d (Real.tanh beta) ↔ Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) := by
  sorry

end Problem367

end

end OAI
