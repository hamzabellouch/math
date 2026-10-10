import Mathlib
import OAI.Computability.MinUncut.PCP.PoweringOpinionTables

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open MinUncutGames.Foundations.Complexity

variable {vertices d : Nat}

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

def reverseOffset (d n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  2 * (wordEquiv d (n + 1) ports).val + (if direction then 0 else 1)

def reverseValue (d n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  blockSize d n * vertex.val + reverseOffset d n ports direction

def tailVertex (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Fin vertices :=
  if direction then wordEnd (PortTables.portGraph input) (n + 1) vertex ports else vertex

def headerWords (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Nat :=
  [(tailVertex input n vertex ports direction).val, reverseValue d n vertex ports direction]

theorem table_tail (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringTables.table input n).rows[encodeDart vertices d n (direction, vertex, ports)].tail =
      tailVertex input n vertex ports direction := by
  change (GenericGraphTables.semantics (PoweringTables.table input n)).tail
    (encodeDart vertices d n (direction, vertex, ports)) = _
  rw [PoweringTables.semantics_table]
  change (PoweringTables.mathematicalGraph input n).tail
    ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, vertex, ports))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem table_reverseValue (input : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringTables.table input n).rows[encodeDart vertices d n
      (direction, vertex, ports)].reverseIndex.val = reverseValue d n vertex ports direction := by
  change (GenericGraphTables.reverseAt (PoweringTables.table input n).rows
    (encodeDart vertices d n (direction, vertex, ports))).val = _
  rw [PoweringTables.table_reverse, encodeDart, dartEquiv_val]
  cases direction <;>
    simp [reverseValue, blockSize, reverseOffset, orientationEquiv, Nat.add_assoc] <;> decide

theorem headerWords_eq (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    headerWords input n vertex ports direction =
      [(PoweringTables.table input n).rows[encodeDart vertices d n
        (direction, vertex, ports)].tail.val,
       (PoweringTables.table input n).rows[encodeDart vertices d n
        (direction, vertex, ports)].reverseIndex.val] := by
  rw [table_tail, table_reverseValue]
  rfl

theorem header_relation_bits (input : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (suffix : List Bool) :
    encodeWords (headerWords input n vertex ports direction) ++
      (encodeWords (GenericGraphTables.relationWords
        (PoweringTables.table input n).rows[encodeDart vertices d n
          (direction, vertex, ports)].relation) ++ suffix) =
      encodeWords (GenericGraphTables.rowWords
        (PoweringTables.table input n).rows[encodeDart vertices d n
          (direction, vertex, ports)]) ++ suffix := by
  rw [headerWords_eq, ← List.append_assoc, ← encodeWords_append]
  rfl

end MinUncutGames.Foundations.PCP.PoweringRowHeaderSemantics

end

end OAI
