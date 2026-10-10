import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateArrival

namespace OAI

/-! Column-labelled transfers retain the exact gates and have three gates per column. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaColumnTransfer {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) : List (QMAGate × Fin (width+1)) :=
  cols.flatMap (fun i => (qmaWireSwapGates (l i) (r i)).map (fun g => (g,i)))

theorem qmaColumnTransfer_gates {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) :
    (qmaColumnTransfer l r cols).map Prod.fst =
      qmaTransferGates (cols.map (fun i => (l i,r i))) := by
  induction cols with
  | nil => rfl
  | cons i cols ih =>
    change ((qmaWireSwapGates (l i) (r i)).map (fun g => (g,i)) ++
      qmaColumnTransfer l r cols).map Prod.fst =
      qmaWireSwapGates (l i) (r i) ++ qmaTransferGates (cols.map (fun i => (l i,r i)))
    simp only [List.map_append,List.map_map,Function.comp_def,List.map_id',ih]

theorem qmaColumnTransfer_count {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) (j : Fin (width+1)) :
    ((qmaColumnTransfer l r cols).filter (fun p => decide (p.2 = j))).length =
      3*(cols.filter (fun i => decide (i = j))).length := by
  induction cols with
  | nil => simp [qmaColumnTransfer]
  | cons i cols ih =>
    change (((qmaWireSwapGates (l i) (r i)).map (fun g => (g,i)) ++
      qmaColumnTransfer l r cols).filter (fun p => decide (p.2 = j))).length = _
    rw [List.filter_append,List.length_append,ih]
    by_cases hij : i = j <;> simp [qmaWireSwapGates,hij,Nat.mul_add,Nat.add_comm]

theorem qmaColumnTransfer_member {width work : ℕ} (l r : Fin (width+1) → Fin (work+1))
    (cols : List (Fin (width+1))) (g : QMAGate) (j : Fin (width+1))
    (h : (g,j) ∈ qmaColumnTransfer l r cols) :
    j ∈ cols ∧ g ∈ qmaWireSwapGates (l j) (r j) := by
  obtain ⟨i,hi,hh⟩ := List.mem_flatMap.mp h
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hh
  have hij : i = j := congrArg Prod.snd he
  have hkg : k = g := congrArg Prod.fst he
  subst i
  subst k
  exact ⟨hi,hk⟩

end ContinuumCoulomb

end

end OAI
