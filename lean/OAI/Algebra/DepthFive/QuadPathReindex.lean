import OAI.Algebra.DepthFive.PairingPartition
import OAI.Algebra.DepthFive.PairingShifts

namespace OAI

namespace Problem335.Pairings

open scoped BigOperators

/-- Zip four independently indexed paths into one path of quadruple labels. -/
def gatherPaths {ι α : Type*} (p q r s : ι → α) : ι → Labels α :=
  fun i => ⟨p i, q i, r i, s i⟩

/-- Four paths and a single quadruple-labelled path contain exactly the same data. -/
def quadPathsEquiv (ι α : Type*) :
    ((ι → α) × (ι → α) × (ι → α) × (ι → α)) ≃ (ι → Labels α) where
  toFun x := gatherPaths x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun x := (fun i => (x i).p, fun i => (x i).q,
    fun i => (x i).r, fun i => (x i).s)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex the four finite path loops without changing any weight. -/
theorem sum_quadPaths {ι α R : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [AddCommMonoid R] (F : (ι → Labels α) → R) :
    (∑ p : ι → α, ∑ q : ι → α, ∑ r : ι → α, ∑ s : ι → α,
      F (gatherPaths p q r s)) = ∑ x : ι → Labels α, F x := by
  classical
  simpa only [Fintype.sum_prod_type, quadPathsEquiv] using
    (Fintype.sum_equiv (quadPathsEquiv ι α)
      (fun x => F (gatherPaths x.1 x.2.1 x.2.2.1 x.2.2.2)) F
      (fun _ => rfl))

/-- Reindex a restricted four-path sum as a sum over the corresponding subtype. -/
theorem sum_quadPaths_subtype {ι α R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [AddCommMonoid R] (P : (ι → Labels α) → Prop)
    [DecidablePred P] (F : (ι → Labels α) → R) :
    (∑ p : ι → α, ∑ q : ι → α, ∑ r : ι → α, ∑ s : ι → α,
      if P (gatherPaths p q r s) then F (gatherPaths p q r s) else 0) =
      ∑ x : {x : ι → Labels α // P x}, F x.1 := by
  classical
  rw [sum_quadPaths (fun x => if P x then F x else 0), ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro x; simp) F

/-- A single path with its two external vertices fixed at `a`. -/
def closePath {α : Type*} {L : ℕ} (a : α) (p : Fin L → α) :
    Fin (L + 2) → α :=
  Fin.cases a (Fin.lastCases a p)

@[simp] theorem closePath_zero {α : Type*} {L : ℕ} (a : α) (p : Fin L → α) :
    closePath a p 0 = a := rfl

@[simp] theorem closePath_last {α : Type*} {L : ℕ} (a : α) (p : Fin L → α) :
    closePath a p (Fin.last (L + 1)) = a := by
  simp [closePath, ← Fin.succ_last]

@[simp] theorem closePath_internal {α : Type*} {L : ℕ}
    (a : α) (p : Fin L → α) (i : Fin L) :
    closePath a p i.castSucc.succ = p i := by
  simp [closePath]

@[simp] theorem closePaths_gather_p {α : Type*} {L : ℕ}
    (a : α) (p q r s : Fin L → α) (i : Fin (L + 2)) :
    (closePaths a (gatherPaths p q r s) i).p = closePath a p i := by
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [closePaths, closePath, gatherPaths, constantLabels, -Fin.succ_last]

@[simp] theorem closePaths_gather_q {α : Type*} {L : ℕ}
    (a : α) (p q r s : Fin L → α) (i : Fin (L + 2)) :
    (closePaths a (gatherPaths p q r s) i).q = closePath a q i := by
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [closePaths, closePath, gatherPaths, constantLabels, -Fin.succ_last]

@[simp] theorem closePaths_gather_r {α : Type*} {L : ℕ}
    (a : α) (p q r s : Fin L → α) (i : Fin (L + 2)) :
    (closePaths a (gatherPaths p q r s) i).r = closePath a r i := by
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [closePaths, closePath, gatherPaths, constantLabels, -Fin.succ_last]

@[simp] theorem closePaths_gather_s {α : Type*} {L : ℕ}
    (a : α) (p q r s : Fin L → α) (i : Fin (L + 2)) :
    (closePaths a (gatherPaths p q r s) i).s = closePath a s i := by
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [closePaths, closePath, gatherPaths, constantLabels, -Fin.succ_last]

/-- The canonical layer labels are exactly the coordinates of the four closed paths. -/
theorem layerLabels_gatherPaths {α : Type*} {L : ℕ}
    (a : α) (p q r s : Fin L → α) (t : Fin (L + 1)) :
    layerLabels a (gatherPaths p q r s) t =
      ⟨edgeCoordinates (closePath a p) t, edgeCoordinates (closePath a q) t,
        edgeCoordinates (closePath a r) t, edgeCoordinates (closePath a s) t⟩ := by
  apply Labels.ext <;> simp [layerLabels, zipLabels, edgeCoordinates]

end Problem335.Pairings

end OAI
