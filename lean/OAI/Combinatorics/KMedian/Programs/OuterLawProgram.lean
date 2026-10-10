import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseOuterLaw
import OAI.Combinatorics.KMedian.Rounding.SignedPreparationProgram
import OAI.Combinatorics.KMedian.Rounding.GridRoundingProgram

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  q : Fin m → ℚ
  c_unit : ∀ e,0≤c e ∧ c e≤1
  q_nonnegative : ∀ e,0≤q e
abbrev Raw := SparseSignedPreparation.Program.Raw
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),(List.ofFn x.c,List.ofFn x.q)))
abbrev Input.encode (x : Input) := enc x.raw
def Input.signed (x : Input) : SparseSignedPreparation.Program.Input :=
  ⟨x.n,x.m,x.D,x.c,SparseGridRounding.fraction x.q,SparseGridRounding.fraction_unit x.q x.q_nonnegative,x.c_unit⟩
def post (x : Raw) : Raw := (x.1,(x.2.1,(x.2.2.1,SparseGridRounding.Program.fractionRow x.2.2.2)))
@[fun_prop] theorem post_poly : Poly post := by unfold post; fun_prop
noncomputable def signedProgram : PolyProgram Input.encode SparseSignedPreparation.Program.Input.encode Input.signed :=
  post_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [post,Input.raw,SparseGridRounding.Program.fractionRow_list,
      SparseSignedPreparation.Program.Input.encode,SparseSignedPreparation.Program.Input.raw,Input.signed])
def Input.result (x : Input) : Data SparseSignedPreparation.Program.StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.q x.c_unit x.q_nonnegative)).1,
    (law x.D x.c x.q x.c_unit x.q_nonnegative).states.toList.map SparseSignedPreparation.Program.view)
noncomputable def program : PolyProgram Input.encode (enc : Data SparseSignedPreparation.Program.StateRaw → List Bool) Input.result :=
  (signedProgram.comp SparseSignedPreparation.Program.program).congr _ (fun _ => rfl)
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
