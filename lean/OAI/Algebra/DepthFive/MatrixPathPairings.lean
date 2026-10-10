import OAI.Algebra.DepthFive.MatrixPathVertices
import OAI.Algebra.DepthFive.RelaxedPaths

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.Pairings

variable {α β σ : Type*}

/-- Apply a representation equivalence independently to the four paths. -/
def matrixPathLabelsEquiv (e : α ≃ β) : Labels α ≃ Labels β where
  toFun x := ⟨e x.p, e x.q, e x.r, e x.s⟩
  invFun x := ⟨e.symm x.p, e.symm x.q, e.symm x.r, e.symm x.s⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp

/-- Transpose four vertex functions into four labels at each vertex. -/
def matrixPathFunctionEquiv (d : ℕ) : Labels (Fin d → α) ≃ (Fin d → Labels α) where
  toFun x t := ⟨x.p t, x.q t, x.r t, x.s t⟩
  invFun x := ⟨fun t => (x t).p, fun t => (x t).q, fun t => (x t).r, fun t => (x t).s⟩
  left_inv x := by cases x; rfl
  right_inv x := by funext t; apply Labels.ext <;> rfl

/-- Quadruples of exact enumerated matrix paths have the internal-label representation
used by `RelaxedPaths` and `CompatiblePaths`. -/
def quadruplePathIndexEquiv [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) :
    (Fin d → Labels α) ≃ Labels (Fin (matrixEntryPaths (List.ofFn labels) a a).length) :=
  (matrixPathFunctionEquiv d).symm.trans
    (matrixPathLabelsEquiv (internalPathEquiv d labels a a))

@[simp] theorem quadruplePathIndexEquiv_get_p [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α) :
    (matrixEntryPaths (List.ofFn labels) a a).get (quadruplePathIndexEquiv d labels a x).p =
      internalPathEdges labels a a (fun t => (x t).p) :=
  get_internalPathEquiv d labels a a _

@[simp] theorem quadruplePathIndexEquiv_get_q [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α) :
    (matrixEntryPaths (List.ofFn labels) a a).get (quadruplePathIndexEquiv d labels a x).q =
      internalPathEdges labels a a (fun t => (x t).q) :=
  get_internalPathEquiv d labels a a _

@[simp] theorem quadruplePathIndexEquiv_get_r [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α) :
    (matrixEntryPaths (List.ofFn labels) a a).get (quadruplePathIndexEquiv d labels a x).r =
      internalPathEdges labels a a (fun t => (x t).r) :=
  get_internalPathEquiv d labels a a _

@[simp] theorem quadruplePathIndexEquiv_get_s [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α) :
    (matrixEntryPaths (List.ofFn labels) a a).get (quadruplePathIndexEquiv d labels a x).s =
      internalPathEdges labels a a (fun t => (x t).s) :=
  get_internalPathEquiv d labels a a _

/-- Coordinate projections commute with adjoining the fixed external vertices. -/
theorem project_closePaths (d : ℕ) (a : α) (x : Fin d → Labels α)
    (proj : Labels α → α) (hp : ∀ a, proj (constantLabels a) = a) :
    (fun t => proj (closePaths a x t)) =
      Fin.cons a (Fin.snoc (fun t => proj (x t)) a) := by
  funext t
  refine Fin.cases ?_ (fun k => ?_) t
  · simp [closePaths, hp]
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [closePaths, -Fin.succ_last, hp]
    · simp [closePaths]

/-- Exact ordered edges after projecting any of the four closed coordinate paths. -/
theorem internalPathEdges_project_closePaths (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α)
    (proj : Labels α → α) (hp : ∀ a, proj (constantLabels a) = a) :
    internalPathEdges labels a a (fun t => proj (x t)) =
      List.ofFn (fun t : Fin (d + 1) =>
        (labels t, proj (closePaths a x t.castSucc), proj (closePaths a x t.succ))) := by
  have h := project_closePaths d a x proj hp
  unfold internalPathEdges
  apply congrArg List.ofFn
  funext t
  have hleft := congrFun h t.castSucc
  have hright := congrFun h t.succ
  rw [Fin.cons_succ] at hright
  rw [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc] at hleft
  rw [hleft, hright]

/-- The four-field record is a nested Cartesian product. -/
def matrixPathLabelsProdEquiv : Labels α ≃ α × α × α × α where
  toFun x := (x.p, x.q, x.r, x.s)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨p,q,r,s⟩; rfl

/-- A sum over four-field records is precisely the iterated fourfold sum. -/
theorem sum_matrixPathLabels [Fintype α] {R : Type*} [AddCommMonoid R]
    (f : Labels α → R) :
    (∑ x : Labels α, f x) = ∑ p : α, ∑ q : α, ∑ r : α, ∑ s : α, f ⟨p,q,r,s⟩ := by
  simpa only [Fintype.sum_prod_type, matrixPathLabelsProdEquiv, Equiv.coe_fn_symm_mk] using
    (Equiv.sum_comp (matrixPathLabelsProdEquiv (α := α)).symm f).symm

/-- Reindex the complete four-path sum into the exact internal-label space used by
pairing classification. No positivity or compatibility premise is required. -/
theorem sum_four_matrixEntryPaths_eq [Fintype α] [DecidableEq α]
    {R : Type*} [AddCommMonoid R] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α)
    (f : List (σ × α × α) → List (σ × α × α) →
      List (σ × α × α) → List (σ × α × α) → R) :
    (∑ p : Fin (matrixEntryPaths (List.ofFn labels) a a).length,
      ∑ q : Fin (matrixEntryPaths (List.ofFn labels) a a).length,
      ∑ r : Fin (matrixEntryPaths (List.ofFn labels) a a).length,
      ∑ s : Fin (matrixEntryPaths (List.ofFn labels) a a).length,
        f ((matrixEntryPaths (List.ofFn labels) a a).get p)
          ((matrixEntryPaths (List.ofFn labels) a a).get q)
          ((matrixEntryPaths (List.ofFn labels) a a).get r)
          ((matrixEntryPaths (List.ofFn labels) a a).get s)) =
      ∑ x : Fin d → Labels α,
        f (internalPathEdges labels a a (fun t => (x t).p))
          (internalPathEdges labels a a (fun t => (x t).q))
          (internalPathEdges labels a a (fun t => (x t).r))
          (internalPathEdges labels a a (fun t => (x t).s)) := by
  let g : Labels (Fin (matrixEntryPaths (List.ofFn labels) a a).length) → R :=
    fun x => f ((matrixEntryPaths (List.ofFn labels) a a).get x.p)
      ((matrixEntryPaths (List.ofFn labels) a a).get x.q)
      ((matrixEntryPaths (List.ofFn labels) a a).get x.r)
      ((matrixEntryPaths (List.ofFn labels) a a).get x.s)
  calc
    _ = ∑ x, g x := (sum_matrixPathLabels g).symm
    _ = _ := by
      simpa only [g, quadruplePathIndexEquiv_get_p, quadruplePathIndexEquiv_get_q,
        quadruplePathIndexEquiv_get_r, quadruplePathIndexEquiv_get_s] using
        (Equiv.sum_comp (quadruplePathIndexEquiv d labels a) g).symm

end Problem335.Pairings

end

end OAI
