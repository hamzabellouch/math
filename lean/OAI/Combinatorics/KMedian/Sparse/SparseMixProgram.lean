import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMixture
import OAI.Combinatorics.KMedian.Sparse.SparseBindProgram

namespace OAI


                                        
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly
variable {α A : Type}

def mixData (x : Data A × Data A) : Data A := bindData ((2,[1,1]),[x.1,x.2])

 theorem mixData_raw (μ ν : SparseIntegerLaw α) (view : α → A) :
    mixData (((raw μ).1,μ.states.toList.map view),((raw ν).1,ν.states.toList.map view))=
      ((raw (μ.mix ν)).1,(μ.mix ν).states.toList.map view) := by
  have h := bindData_raw (fair) (fun a => if a.val=0 then μ else ν) view
  simpa [mixData,mix,raw,fair,List.ofFn_succ] using h

@[fun_prop] theorem mixData_poly [Coding A] [Inhabited A] : Poly (mixData (A:=A)) := by
  unfold mixData
  fun_prop
end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
