import Mathlib
import OAI.Combinatorics.KMedian.Compression.ComputedIntegerKernel
import OAI.Combinatorics.KMedian.Compression.GaussianBinaryProgram
import OAI.Combinatorics.KMedian.Compression.IntegerListProgram

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.IntegerProgram
open Binary Binary.PolyProgram
abbrev Row := IntegerList.Row
abbrev Rows := IntegerList.Rows
abbrev er := IntegerList.er
abbrev em := IntegerList.em
abbrev ed := encodePair ListOperation.eslots em

structure Input where
  r : ℕ
  n : ℕ
  V : Fin r → Fin n → ℤ
  underdetermined : r < n

def Input.raw (I : Input) : List Unit × Rows :=
  (List.replicate I.n (),List.ofFn (fun i => List.ofFn (I.V i)))
abbrev Input.encode (I : Input) := ed I.raw

def Input.rational (I : Input) : ListOperation.Input :=
  ⟨I.r,I.n,tabulate (fun i j => (I.V i j:ℚ)),I.underdetermined⟩
def castRows (vs : Rows) : ListOperation.Rows := vs.map (List.map (fun z : ℤ => (z:ℚ)))

theorem castRows_ofFn {r n : ℕ} (V : Fin r → Fin n → ℤ) :
    castRows (List.ofFn (fun i => List.ofFn (V i)))=ListOperation.matrix (fun i j => (V i j:ℚ)) := by
  simp only [castRows,List.map_ofFn,Function.comp_def,ListOperation.matrix]

noncomputable def rationalProgram : PolyProgram Input.encode ListOperation.Input.encode Input.rational := by
  let cast := (ratOfInt.listMap 0).listMap []
  let raw := (cast.second ListOperation.eslots)
  exact raw.recode Input.raw (fun _ => rfl) (fun I => by
    change ListOperation.edata (List.replicate I.n (),castRows (List.ofFn (fun i => List.ofFn (I.V i)))) = _
    rw [castRows_ofFn]
    simp only [ListOperation.Input.encode,ListOperation.Input.raw,Input.rational,values_tabulate])

def Input.result (I : Input) : Row := List.ofFn (computedIntegerKernel I.r I.n I.V)

noncomputable def kernelProgram : PolyProgram Input.encode er Input.result :=
  ((rationalProgram.comp ListOperation.kernelProgram).comp IntegerList.numeratorsProgram).congr _ (fun I => by
    simp only [Function.comp_apply,ListOperation.Input.result,ListOperation.kernelList,IntegerList.numerators_ofFn]
    unfold Input.result computedIntegerKernel
    simp only [Vector.getElem_ofFn]
    rfl)
end MetricKMedian.Gaussian.IntegerProgram
end

end OAI
