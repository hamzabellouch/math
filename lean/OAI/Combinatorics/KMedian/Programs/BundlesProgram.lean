import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseBundleLaw
import OAI.Combinatorics.KMedian.Rounding.GridRoundingProgram
import OAI.Combinatorics.KMedian.Process.CountRunProgram

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram SparseCounts.Program
abbrev qr := encodeList Ratio.encode
abbrev qt := encodeList qr
abbrev eqi := encodePair (encodeList (fun _ : Unit => [])) qt

structure QInput where
  n : ℕ
  m : ℕ
  q : Fin n → Fin m → ℚ
  feasible : ∀ h i, 0≤q h i

def QInput.raw (x : QInput) : List Unit × List (List ℚ) :=
  (List.replicate x.n (),List.ofFn fun i => List.ofFn fun h => x.q h i)
abbrev QInput.encode (x : QInput) := eqi x.raw

def QInput.column (x : QInput) (i : Fin x.m) : SparseGridRounding.Program.Input :=
  ⟨x.n,fun h => x.q h i,fun h => x.feasible h i⟩
def QInput.columns (x : QInput) : List SparseGridRounding.Program.Input := List.ofFn x.column
def emptyColumn : SparseGridRounding.Program.Input := ⟨0,Fin.elim0,fun i => Fin.elim0 i⟩
def QInput.input (x : QInput) : Input := ⟨x.n,x.m,(fun j => SparseGridRounding.law (fun i => x.q i j))⟩
def QInput.result (x : QInput) : Data SparseCounts.ListOperation.Table :=
  (((SparseBundles.law x.q).law.denominator,List.ofFn (SparseBundles.law x.q).law.numerator),
    (SparseBundles.law x.q).states.toList.map SparseCounts.ListOperation.view)

noncomputable def columnsProgram : PolyProgram QInput.encode (encodeList SparseGridRounding.Program.Input.encode) QInput.columns :=
  (snd (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun x => by
    change qt (List.ofFn (fun i => List.ofFn (x.column i).q))=
      encodeList SparseGridRounding.Program.Input.encode (List.ofFn x.column)
    rw [show List.ofFn (fun i => List.ofFn (x.column i).q)=
      (List.ofFn x.column).map (fun c => List.ofFn c.q) by rw [List.map_ofFn]; rfl]
    exact RoundingProgram.encodeList_map qr (fun c : SparseGridRounding.Program.Input => List.ofFn c.q) _)

noncomputable def inputProgram : PolyProgram QInput.encode Input.encode QInput.input := by
  let n := (fst (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun _ => rfl)
  let cols := columnsProgram.comp (SparseGridRounding.Program.program.listMap emptyColumn)
  exact (n.fanout cols).recode id (fun _ => rfl) (fun x => by
    change ei (x.raw.1,x.columns.map SparseGridRounding.Program.Input.result)=Input.encode x.input
    simp only [QInput.columns,List.map_ofFn,Function.comp_def]
    rfl)

noncomputable def lawProgram : PolyProgram QInput.encode (ed SparseCounts.ListOperation.et) QInput.result := by
  let get : PolyProgram State.encode (ed SparseCounts.ListOperation.et) (fun x : State => (x.raw view).2) :=
    (snd Context.encode (ed SparseCounts.ListOperation.et)).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
  exact (inputProgram.comp runStateProgram |>.comp get).congr _ (fun _ => rfl)
end MetricKMedian.SparseBundles.Program
end

end OAI
