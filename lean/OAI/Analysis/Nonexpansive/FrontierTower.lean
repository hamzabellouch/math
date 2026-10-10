import OAI.Analysis.Nonexpansive.TreeFrontier

namespace OAI

/-!
# From actual finite extensions to one infinite evaluated tree

A tower records the concrete successor extension at every finite stage.
Its coherence equalities identify each new frontier with that extension.
The infinite tree, its positive weights, and its nonlinear evaluation are
extracted from these records. Finite and infinite evaluation agree by
induction on the number of extensions.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TreeFrontier

variable {K : Set X}

/-- Transport a node map through equality of the concrete frontiers. -/
theorem map_transport {F G : TreeFrontier K} (h : F = G) (p : Fin F.size) :
    F.map p = G.map (finCongr (congrArg TreeFrontier.size h) p) := by
  subst G
  rfl

/-- Transport a cutoff assignment through equality of concrete frontiers. -/
theorem evaluate_transport {F G : TreeFrontier K} (h : F = G)
    (H : Fin F.size → K) :
    F.evaluate H =
      G.evaluate (fun p => H ((finCongr (congrArg TreeFrontier.size h)).symm p)) := by
  subst G
  rfl

theorem evaluate_eq_root_of_eq {F : TreeFrontier K} {hK : Convex ℝ K}
    (h : F = TreeFrontier.root hK) (H : Fin F.size → K) :
    F.evaluate H = H ⟨0, F.size_pos⟩ := by
  subst F
  rfl

theorem map_eq_id_of_eq_root {F : TreeFrontier K} {hK : Convex ℝ K}
    (h : F = TreeFrontier.root hK) (p : Fin F.size) : F.map p = id := by
  subst F
  rfl

end TreeFrontier

/-- A coherent sequence of actual finite extensions, beginning with the root. -/
structure FrontierTower (K : Set X) where
  convex : Convex ℝ K
  frontier : ℕ → TreeFrontier K
  step : (k : ℕ) → FrontierExtension (frontier k)
  zero : frontier 0 = TreeFrontier.root convex
  next : ∀ k, frontier (k + 1) = (step k).toFrontier

namespace FrontierTower

variable {K : Set X} (S : FrontierTower K)

theorem next_size (k : ℕ) : (S.frontier (k + 1)).size = (S.step k).size :=
  congrArg TreeFrontier.size (S.next k)

/-- The canonical identification of next-level nodes with the actual extension. -/
def nextNode (k : ℕ) : Fin (S.frontier (k + 1)).size ≃ Fin (S.step k).size :=
  finCongr (S.next_size k)

@[simp] theorem nextNode_val (k : ℕ) (v : Fin (S.frontier (k + 1)).size) :
    (S.nextNode k v).val = v.val := rfl

@[simp] theorem nextNode_symm_val (k : ℕ) (v : Fin (S.step k).size) :
    ((S.nextNode k).symm v).val = v.val := rfl

theorem nextNode_monotone (k : ℕ) : Monotone (S.nextNode k) := by
  intro a b hab
  exact hab

/-- The single infinite ordered tree extracted from all concrete levels. -/
def toOrderedTree : OrderedTree where
  size := fun k => (S.frontier k).size
  size_pos := fun k => (S.frontier k).size_pos
  size_zero := congrArg TreeFrontier.size S.zero
  parent := fun k c => (S.step k).parent (S.nextNode k c)
  parent_monotone := fun k => (S.step k).parent_monotone.comp (S.nextNode_monotone k)
  parent_surjective := fun k => (S.step k).parent_surjective.comp (S.nextNode k).surjective

@[simp] theorem toOrderedTree_size (k : ℕ) :
    S.toOrderedTree.size k = (S.frontier k).size := rfl

@[simp] theorem toOrderedTree_parent (k : ℕ) (c : S.toOrderedTree.Node (k + 1)) :
    S.toOrderedTree.parent k c = (S.step k).parent (S.nextNode k c) := rfl

/-- Extract the actual positive weights chosen by every finite extension. -/
def toWeightedTree : WeightedTree S.toOrderedTree where
  weight := fun k c => (S.step k).weight (S.nextNode k c)
  weight_pos := fun k c => (S.step k).weight_pos (S.nextNode k c)
  weight_sum := by
    classical
    intro k p
    dsimp +instances only [toOrderedTree, OrderedTree.Node] at p ⊢
    simp only [Finset.sum_filter]
    calc
      _ = ∑ c : Fin (S.step k).size,
          if (S.step k).parent c = p then (S.step k).weight c else 0 :=
        (S.nextNode k).sum_comp _
      _ = 1 := by simpa only [Finset.sum_filter] using (S.step k).weight_sum p

@[simp] theorem toWeightedTree_weight (k : ℕ) (c : S.toOrderedTree.Node (k + 1)) :
    S.toWeightedTree.weight k c = (S.step k).weight (S.nextNode k c) := rfl

/-- The final nonlinear evaluator uses exactly the maps stored in the frontiers. -/
def toEvaluation : TreeEvaluation S.toWeightedTree K where
  convex := S.convex
  map := fun k v => (S.frontier k).map v
  nonexpansive := fun k v => (S.frontier k).nonexpansive v

@[simp] theorem toEvaluation_map (k : ℕ) (v : S.toOrderedTree.Node k) :
    S.toEvaluation.map k v = (S.frontier k).map v := rfl

theorem toEvaluation_map_succ (k : ℕ) (v : S.toOrderedTree.Node (k + 1)) :
    S.toEvaluation.map (k + 1) v = (S.step k).map (S.nextNode k v) :=
  TreeFrontier.map_transport (S.next k) v

@[simp] theorem toEvaluation_map_zero (v : S.toOrderedTree.Node 0) :
    S.toEvaluation.map 0 v = id :=
  TreeFrontier.map_eq_id_of_eq_root S.zero v

/-- Reindexing the new children preserves their actual convex average. -/
theorem childAverage_agreement (k : ℕ) (H : S.toOrderedTree.Node (k + 1) → K)
    (p : S.toOrderedTree.Node k) :
    S.toEvaluation.childAverage k H p =
      (S.step k).childAverage (fun c => H ((S.nextNode k).symm c)) p := by
  classical
  dsimp only [toOrderedTree, OrderedTree.Node] at H p ⊢
  apply Subtype.ext
  dsimp only [TreeEvaluation.childAverage, FrontierExtension.childAverage,
    toEvaluation, toWeightedTree, toOrderedTree, OrderedTree.Node]
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (S.nextNode k)
  intro c
  simp only [Equiv.symm_apply_apply]

theorem collapse_agreement (k : ℕ) (H : S.toOrderedTree.Node (k + 1) → K) :
    S.toEvaluation.collapse k H =
      (S.step k).collapse (fun c => H ((S.nextNode k).symm c)) := by
  funext p
  change (S.frontier k).map p (S.toEvaluation.childAverage k H p) =
    (S.frontier k).map p ((S.step k).childAverage (fun c => H ((S.nextNode k).symm c)) p)
  rw [S.childAverage_agreement]

theorem frontier_zero_evaluate (H : S.toOrderedTree.Node 0 → K) :
    (S.frontier 0).evaluate H = H S.toOrderedTree.root :=
  TreeFrontier.evaluate_eq_root_of_eq S.zero H

/-- Successor frontier evaluation is its recorded predecessor composition. -/
theorem frontier_succ_evaluate (k : ℕ) (H : S.toOrderedTree.Node (k + 1) → K) :
    (S.frontier (k + 1)).evaluate H =
      (S.frontier k).evaluate
        ((S.step k).collapse (fun c => H ((S.nextNode k).symm c))) :=
  TreeFrontier.evaluate_transport (S.next k) H

/-- The finite prediction evaluator equals the final infinite-tree evaluator. -/
theorem evaluate_agreement (k : ℕ) (H : S.toOrderedTree.Node k → K) :
    (S.frontier k).evaluate H = S.toEvaluation.evaluate k H := by
  induction k with
  | zero => exact S.frontier_zero_evaluate H
  | succ k ih =>
      calc
        (S.frontier (k + 1)).evaluate H =
            (S.frontier k).evaluate
              ((S.step k).collapse (fun c => H ((S.nextNode k).symm c))) :=
          S.frontier_succ_evaluate k H
        _ = S.toEvaluation.evaluate k
            ((S.step k).collapse (fun c => H ((S.nextNode k).symm c))) := ih _
        _ = S.toEvaluation.evaluate k (S.toEvaluation.collapse k H) := by
          rw [S.collapse_agreement]
        _ = S.toEvaluation.evaluate (k + 1) H := rfl

/-- Agreement also holds after applying each already chosen cutoff map once. -/
theorem evaluate_map_agreement (k : ℕ) (H : S.toOrderedTree.Node k → K) :
    (S.frontier k).evaluate (fun p => (S.frontier k).map p (H p)) =
      S.toEvaluation.evaluate k (fun p => S.toEvaluation.map k p (H p)) :=
  S.evaluate_agreement k _

end FrontierTower
end ReflexiveFixedPoints

end

end OAI
