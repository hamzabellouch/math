import OAI.Analysis.CircleDomains.Selection.JumpChainEdges
import OAI.Analysis.CircleDomains.Selection.FiniteJumpPattern
import OAI.Analysis.CircleDomains.Selection.JumpTollLowerBound

namespace OAI

/-! Concrete finite chains grouped into true-path blocks separated by
old jumps. The finite code records old disk labels and new-jump counts. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

abbrev BoundedBlockPattern (I : Type*) (n : ℕ) :=
  Σq : Fin (n+1), (Fin q.val → I) × (Fin (q.val+1) → Fin (n+1))

def blockAnchors {X I : Type*} {n : ℕ} (F H : Set X) (O : I → Set X)
    (P : BoundedBlockPattern I n) : Fin (P.1.val+2) → Set X :=
  Fin.cons F (Fin.snoc (fun i => O (P.2.1 i)) H)

@[simp] theorem blockAnchors_zero {X I : Type*} {n : ℕ} (F H : Set X)
    (O : I → Set X) (P : BoundedBlockPattern I n) : blockAnchors F H O P 0 = F := by
  simp [blockAnchors]

@[simp] theorem blockAnchors_last {X I : Type*} {n : ℕ} (F H : Set X)
    (O : I → Set X) (P : BoundedBlockPattern I n) :
    blockAnchors F H O P (Fin.last (P.1.val+1)) = H := by
  simp [blockAnchors]

@[simp] theorem blockAnchors_internal {X I : Type*} {n : ℕ} (F H : Set X)
    (O : I → Set X) (P : BoundedBlockPattern I n) (i : Fin P.1.val) :
    blockAnchors F H O P i.succ.castSucc = O (P.2.1 i) := by
  simp [blockAnchors, Fin.castSucc_succ]

theorem blockAnchors_frontier {X I : Type*} [TopologicalSpace X] {n : ℕ}
    (F H U : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (hF : frontier F ⊆ U) (hH : frontier H ⊆ U) (hO : ∀i, frontier (O i) ⊆ U) :
    ∀i, frontier (blockAnchors F H O P i) ⊆ U := by
  intro i
  refine Fin.cases (by simpa using hF) (fun j => ?_) i
  refine Fin.lastCases (by simpa [blockAnchors] using hH) (fun j => ?_) j
  simpa [blockAnchors] using hO (P.2.1 j)

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

structure JumpBlockCode (d : PathCodeData X Y) (P : BoundedBlockPattern I n) where
  paths : ∀b : Fin (P.1.val+1), Fin ((P.2.2 b).val+1) → TaggedPhysicalPath d
  disks : ∀b : Fin (P.1.val+1), Fin (P.2.2 b).val → Set X

structure IsJumpBlockCode (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) : Prop where
  allowed : ∀b j, AllowedTaggedPath d ν N ((Z.paths b j).1.val, (Z.paths b j).2)
  start : ∀b, (Z.paths b 0).1.val ⊥ ∈ blockAnchors F H O P b.castSucc ∩ d.quotientDomain
  finish : ∀b, (Z.paths b (Fin.last (P.2.2 b).val)).1.val ⊤ ∈
    blockAnchors F H O P b.succ ∩ d.quotientDomain
  left : ∀b i, (Z.paths b i.castSucc).1.val ⊤ ∈ Z.disks b i
  right : ∀b i, (Z.paths b i.succ).1.val ⊥ ∈ Z.disks b i
  meets : ∀b i, (Z.disks b i ∩ B).Nonempty

def jumpBlockCost (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞)
    (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) : ℝ≥0∞ :=
  (∑b, ((∑j, physicalTollCost d g m (Z.paths b j).1) +
    ∑i, fixedWidthJumpToll B m r τ (Z.disks b i))) + ∑i, T (P.2.1 i)

end CircleDomainRigidity

end

end OAI
