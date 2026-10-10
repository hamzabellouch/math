import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringEnumeration
import OAI.Computability.VertexCover.PCP.PoweringOpinionTables
import OAI.Computability.VertexCover.PCP.GenericGraphTables

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

def mathematicalGraph {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    ConstraintGraph (Fin vertices) (PoweringTest.Dart (Fin vertices) (Fin d) n)
      (PaddedLabel (Fin d) (n + 1) (Fin 64)) :=
  PoweringTest.poweredGraph (PortTables.portGraph input) (PortTables.accepts input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1))

def rowAccepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) : Bool :=
  let rows := PoweringOpinionTables.walkRows (PortTables.portGraph input) n e.2
  let left := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 a)
  let right := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 b)
  if e.1 then PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows right left
    else PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows left right

theorem rowAccepts_eq {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) :
    rowAccepts input n e a b = (mathematicalGraph input n).accepts e
      (decodeLabel d (n + 1) 64 a) (decodeLabel d (n + 1) 64 b) := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowAccepts, mathematicalGraph, PoweringTest.poweredGraph, Bool.false_eq_true,
      ite_false, ite_true, PoweringOpinionTables.rowsAccepts_walkRows]

def table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.Table (labelCount d n) :=
  GenericGraphTables.ofEnumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
    (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64)

@[simp] theorem table_vertices {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).vertices = vertices := rfl

@[simp] theorem table_darts {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).darts = dartCount vertices d n := rfl

theorem semantics_table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.semantics (table input n) =
      GenericGraphTables.enumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
        (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) :=
  GenericGraphTables.semantics_ofGraph _

theorem table_accepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (dartCount vertices d n)) (a b : Fin (labelCount d n)) :
    GenericGraphTables.acceptsAt (table input n).rows i a b =
      rowAccepts input n (decodeDart vertices d n i) a b := by
  change (GenericGraphTables.semantics (table input n)).accepts i a b = _
  rw [semantics_table]
  exact (rowAccepts_eq input n (decodeDart vertices d n i) a b).symm

theorem table_reverse {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (direction : Bool) (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    GenericGraphTables.reverseAt (table input n).rows (encodeDart vertices d n (direction, w)) =
      encodeDart vertices d n (!direction, w) := by
  change (GenericGraphTables.semantics (table input n)).reverse _ = _
  rw [semantics_table]
  change dartEquiv vertices d n ((mathematicalGraph input n).reverse
      ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, w)))) =
    dartEquiv vertices d n (!direction, w)
  rw [(dartEquiv vertices d n).symm_apply_apply]
  rfl

def outputBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) : List Bool :=
  GenericGraphTables.tableBits (table input n)

def transform (d n : Nat) (input : PortTables.Input d) : GenericGraphTables.Table (labelCount d n) :=
  table input.2 n

end UniqueGames.Foundations.PCP.PoweringTables

end OAI
