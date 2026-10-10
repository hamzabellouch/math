import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWalkErasure
import OAI.Computability.QuantumFactoring.BitStackListFold

namespace OAI

/-! The support compiler retains the last occurrence of each numeric label,
exactly as `List.dedup` does in the mathematical ordered support. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb.QuantumSupportDedup
open ExactQuantumFactoring.BitStackProgram

def insert (a : ℕ) (xs : List ℕ) : List ℕ := if a ∈ xs then xs else a::xs

theorem insert_sublist (a : ℕ) (xs : List ℕ) : insert a xs <+ a::xs := by
  unfold insert
  split
  · exact List.sublist_cons_self _ _
  · exact List.Sublist.refl _

theorem fold_sublist (xs ys : List ℕ) :
    xs.foldl (fun zs a => insert a zs) ys <+ xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => exact List.Sublist.refl _
  | cons a xs ih =>
    simp only [List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    exact (ih (insert a ys)).trans ((insert_sublist a ys).append_left xs.reverse)

theorem fold_bound (xs ys : List ℕ) :
    (listCode Nat.bits (xs.foldl (fun zs a => insert a zs) ys)).length ≤
      (listCode Nat.bits xs).length+(listCode Nat.bits ys).length := by
  have h := QuantumWalkErasure.listCode_length_sublist Nat.bits (fold_sublist xs ys)
  have ha := listCode_length_append Nat.bits xs.reverse ys
  rw [listCode_length_rev] at ha
  omega

theorem foldr_eq (xs : List ℕ) : xs.foldr insert []=xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons,ih,List.dedup_cons']
    rfl

noncomputable opaque insertProgram :
    Procedure (prodCode Nat.bits (listCode Nat.bits)) (listCode Nat.bits)
      (fun x => insert x.1 x.2) :=
  (Procedure.conditional (QuantumFiniteMembership.memberProgram Nat.bits 0 Procedure.binaryEq)
    (Procedure.second Nat.bits (listCode Nat.bits)) (Procedure.listCons Nat.bits)).congrFun
      (by intro x; simp only [insert,decide_eq_true_eq])

noncomputable opaque foldProgram :
    Procedure (prodCode (listCode Nat.bits) (listCode Nat.bits)) (listCode Nat.bits)
      (fun x => x.1.foldl (fun zs a => insert a zs) x.2) :=
  Procedure.foldList 0 insertProgram Polynomial.X (by
    intro xs ys i
    have h := fold_bound (xs.take i) ys
    have ht := listCode_length_take_le Nat.bits i xs
    simp only [Polynomial.eval_X]
    omega)

noncomputable opaque program : Procedure (listCode Nat.bits) (listCode Nat.bits) List.dedup :=
  (foldProgram.comp ((Procedure.listReverse Nat.bits 0).pair
    (Procedure.constant (listCode Nat.bits) (listCode Nat.bits) []))).congrFun (by
      intro xs
      simp only [Function.comp_apply,List.foldl_reverse,foldr_eq])

end ContinuumCoulomb.QuantumSupportDedup

end

end OAI
