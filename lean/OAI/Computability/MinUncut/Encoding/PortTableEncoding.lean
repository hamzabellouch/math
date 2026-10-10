import Mathlib
import OAI.Computability.MinUncut.PCP.PreprocessingTableSpectral

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PortTables

variable {n d : Nat}

def HasPortTails (rows : GraphTables.Rows n (n * d)) : Prop :=
  ∀ i : Fin (n * d), rows[i].tail = ((rowIndex n d).symm i).1

instance (rows : GraphTables.Rows n (n * d)) : Decidable (HasPortTails rows) := by
  unfold HasPortTails
  infer_instance

@[simp] theorem flatRows_hasPortTails (table : Table n d) : HasPortTails (flatRows table) := by
  intro i
  simp [flatRows]

def ofRows (rows : GraphTables.Rows n (n * d)) (valid : GraphTables.Valid rows) : Table n d where
  reverseIndex := Vector.ofFn (fun i => rows[i].reverseIndex)
  relations := Vector.ofFn (fun i => rows[i].relation)
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    exact valid.1 i
  transpose := by
    intro i a b
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    exact valid.2 i a b

private theorem table_ext {table table' : Table n d}
    (hr : table.reverseIndex = table'.reverseIndex)
    (hp : table.relations = table'.relations) : table = table' := by
  cases table
  cases table'
  cases hr
  cases hp
  rfl

@[simp] theorem ofRows_flatRows (table : Table n d) :
    ofRows (flatRows table) (flatRows_valid table) = table := by
  apply table_ext
  · apply Vector.ext
    intro i hi
    simp [ofRows, flatRows]
  · apply Vector.ext
    intro i hi
    simp [ofRows, flatRows]

def extractInput (ports : Nat) : GraphTables.Table → Option (Input ports)
  | ⟨vertices, darts, rows, valid⟩ =>
      if count_ok : darts = vertices * ports then
        let rows' : GraphTables.Rows vertices (vertices * ports) := count_ok ▸ rows
        let valid' : GraphTables.Valid rows' := by
          cases count_ok
          exact valid
        if HasPortTails rows' then
          some ⟨vertices, ofRows rows' valid'⟩
        else none
      else none

@[simp] theorem extractInput_graphTable (table : Table n d) :
    extractInput d (graphTable table) = some (⟨n, table⟩ : Input d) := by
  simp [extractInput, graphTable]

def decodeInputBits (ports : Nat) (bits : List Bool) : Option (Input ports) :=
  GraphTables.decodeTableBits bits >>= extractInput ports

@[simp] theorem decodeInputBits_inputBits {ports : Nat} (input : Input ports) :
    decodeInputBits ports (inputBits input) = some input := by
  rcases input with ⟨vertices, table⟩
  simp [decodeInputBits, inputBits, tableBits]

def encoding (ports : Nat) : Computability.Encoding (Input ports) Bool where
  encode := inputBits
  decode := decodeInputBits ports
  decode_encode := decodeInputBits_inputBits

theorem inputBits_injective (ports : Nat) : Function.Injective (@inputBits ports) :=
  (encoding ports).encode_injective

end MinUncutGames.Foundations.PCP.PortTables

end

end OAI
