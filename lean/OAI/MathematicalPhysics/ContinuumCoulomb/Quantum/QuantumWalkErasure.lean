import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortChain
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFiniteMembership

namespace OAI

/-! The coarse route's library loop erasure is the explicit right-to-left
finite-list algorithm. This identifies the actual path data needed by the
literal spatial compiler. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb.QuantumWalkErasure
open ExactQuantumFactoring.BitStackProgram

variable {α : Type} [DecidableEq α]

def step (a : α) (xs : List α) : List α :=
  if a ∈ xs then xs.drop (xs.idxOf a) else a::xs

def erase (xs : List α) : List α := xs.foldr step []

@[simp] theorem erase_nil : erase ([] : List α) = [] := rfl
@[simp] theorem erase_cons (a : α) (xs : List α) : erase (a::xs) = step a (erase xs) := rfl

theorem step_sublist (a : α) (xs : List α) : step a xs <+ a::xs := by
  unfold step
  split
  · exact (List.drop_sublist _ _).trans (List.sublist_cons_self _ _)
  · exact List.Sublist.refl _

theorem erase_sublist (xs : List α) : erase xs <+ xs := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons a xs ih =>
    rw [erase_cons]
    exact (step_sublist a (erase xs)).trans (ih.cons_cons a)

omit [DecidableEq α] in
theorem listCode_length_sublist (ea : α → List Bool) {xs ys : List α} (h : xs <+ ys) :
    (listCode ea xs).length ≤ (listCode ea ys).length := by
  induction h with
  | slnil => exact le_rfl
  | cons a h ih =>
    rw [listCode_length_cons]
    omega
  | cons_cons a h ih =>
    simp only [listCode_length_cons]
    omega

variable {G : SimpleGraph α} {a b c : α}

private theorem support_dropUntil (p : G.Walk a b) (h : c ∈ p.support) :
    (p.dropUntil c h).support = p.support.drop (p.support.idxOf c) := by
  have hi := List.idxOf_lt_length_of_mem h
  have hs := p.length_support
  have hib : p.support.idxOf c ≤ p.length := by omega
  rw [SimpleGraph.Walk.dropUntil_eq_drop,SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,Nat.min_eq_left hib]

theorem support_bypass (p : G.Walk a b) : erase p.support = p.bypass.support := by
  induction p with
  | nil => simp [erase,step,SimpleGraph.Walk.bypass]
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.support_cons,erase_cons,ih]
    simp only [step,SimpleGraph.Walk.bypass]
    split_ifs with h
    · exact (support_dropUntil p.bypass h).symm
    · rfl

end QuantumWalkErasure

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem bufferedPath_support_explicit
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (M.bufferedPath hd e).val.support =
      QuantumWalkErasure.erase (M.bufferedWalk hd e).support :=
  (QuantumWalkErasure.support_bypass (M.bufferedWalk hd e)).symm

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
