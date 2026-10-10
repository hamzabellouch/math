import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWalkErasure
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteProgram
import OAI.Computability.QuantumFactoring.BitStackListFold

namespace OAI

/-! The crossing compiler retains one occurrence of each coordinate pair,
with an output bound from the original list. -/

noncomputable section
open scoped List Classical
namespace ContinuumCoulomb.QuantumPairDedup
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def insertPair (a : Pair) (xs : List Pair) : List Pair := if a ∈ xs then xs else a::xs

theorem insert_sublist (a : Pair) (xs : List Pair) : insertPair a xs <+ a::xs := by
  unfold insertPair
  split
  · exact List.sublist_cons_self _ _
  · exact List.Sublist.refl _

theorem fold_sublist (xs ys : List Pair) :
    xs.foldl (fun zs a => insertPair a zs) ys <+ xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => exact List.Sublist.refl _
  | cons a xs ih =>
    simp only [List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    exact (ih (insertPair a ys)).trans ((insert_sublist a ys).append_left xs.reverse)

theorem fold_bound (xs ys : List Pair) :
    (listCode pairCode (xs.foldl (fun zs a => insertPair a zs) ys)).length ≤
      (listCode pairCode xs).length+(listCode pairCode ys).length := by
  have h := QuantumWalkErasure.listCode_length_sublist pairCode (fold_sublist xs ys)
  have ha := listCode_length_append pairCode xs.reverse ys
  rw [listCode_length_rev] at ha
  omega

theorem foldr_eq (xs : List Pair) : xs.foldr insertPair []=xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons,ih,List.dedup_cons']
    by_cases h : a ∈ xs.dedup <;> simp [insertPair,h]

noncomputable opaque insertProgram :
    Procedure (prodCode pairCode (listCode pairCode)) (listCode pairCode)
      (fun x => insertPair x.1 x.2) :=
  (Procedure.conditional (QuantumFiniteMembership.memberProgram pairCode (0,0) QuantumFiniteMembership.pairEqProgram)
    (Procedure.second pairCode (listCode pairCode)) (Procedure.listCons pairCode)).congrFun
      (by intro x; simp only [insertPair,decide_eq_true_eq])

noncomputable opaque foldProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
      (fun x => x.1.foldl (fun zs a => insertPair a zs) x.2) :=
  Procedure.foldList (0,0) insertProgram Polynomial.X (by
    intro xs ys i
    have h := fold_bound (xs.take i) ys
    have ht := listCode_length_take_le pairCode i xs
    simp only [Polynomial.eval_X]
    convert h.trans (Nat.add_le_add_right ht _) using 1)

noncomputable opaque program : Procedure (listCode pairCode) (listCode pairCode) List.dedup :=
  (foldProgram.comp ((Procedure.listReverse pairCode (0,0)).pair
    (Procedure.constant (listCode pairCode) (listCode pairCode) []))).congrFun (by
      intro xs
      simp only [Function.comp_apply,List.foldl_reverse,foldr_eq])

end ContinuumCoulomb.QuantumPairDedup

end

end OAI
