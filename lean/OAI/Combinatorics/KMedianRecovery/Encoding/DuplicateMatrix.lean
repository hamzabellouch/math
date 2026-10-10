import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op2

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix
open WordOperations WordList
variable {n : ℕ}
def forget : Fin (n+n)→Fin n := Fin.append id id
def duplicate (δ : Fin n→Fin n→ℚ) : Fin (n+n)→Fin (n+n)→ℚ :=
  fun i j=>δ (forget i) (forget j)
noncomputable def twice (xs : List Bool) : List Bool := xs++xs
noncomputable def twice_computes : PolyComputes twice := id_computes.append id_computes
noncomputable def run : List Bool→List Bool := twice ∘ map twice
noncomputable def run_computes : PolyComputes run := (map_computes twice_computes).comp twice_computes
lemma row_double (f : Fin n→ℚ) :
    RationalMatrix.rowEncode (fun j : Fin (n+n)=>f (forget j))=
      RationalMatrix.rowEncode f++RationalMatrix.rowEncode f := by
  simp only [RationalMatrix.rowEncode_eq,List.ofFn_add,forget,Fin.append_left',Fin.append_right,id_eq,
    encode_append]
lemma forget_left (i : Fin n) : forget (Fin.castLE (Nat.le_add_right n n) i)=i := Fin.append_left' id id i
lemma forget_right (i : Fin n) : forget (Fin.natAdd n i)=i := Fin.append_right id id i
lemma run_encode (δ : Fin n→Fin n→ℚ) :
    run (RationalMatrix.encode δ)=RationalMatrix.encode (duplicate δ) := by
  change twice (map twice (encode (List.ofFn (fun i=>RationalMatrix.rowEncode (δ i)))))=
    encode (List.ofFn (fun i=>RationalMatrix.rowEncode (fun j=>δ (forget i) (forget j))))
  rw [map_encode,List.map_ofFn,List.ofFn_add]
  simp only [forget_left,forget_right,encode_append,row_double]
  rfl

end MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix

end OAI
