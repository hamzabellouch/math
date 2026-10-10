import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack4

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Set
open WordOperations BinaryArithmetic
noncomputable def pack_computes {xs j v : List Bool→List Bool}
    (hx : PolyComputes xs) (hj : PolyComputes j) (hv : PolyComputes v) :
    PolyComputes (fun x=>pack (xs x) (j x) (v x)) := hx.pair (hj.pair hv)
lemma run_encode (ws : List (List Bool)) (j : ℕ) (hj : j<ws.length) (v : List Bool) :
    run (pack (encode ws) j.bits v)=encode (ws.set j v) := by
  have hh:=run_ofFn ws.get ⟨j,hj⟩ v
  rw [List.ofFn_get] at hh
  rw [hh]
  apply congrArg encode
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_ofFn]
    rw [List.getElem_set]
    split_ifs <;> simp_all [Fin.ext_iff]
end MetricKMedianRecovery.BitMachine.WordList.Set

end OAI
