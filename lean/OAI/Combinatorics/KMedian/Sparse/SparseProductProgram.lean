import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseProduct
import OAI.Combinatorics.KMedian.Rounding.SignedListOperations
import OAI.Combinatorics.KMedian.Sparse.SparseListTrim

namespace OAI


                                            
section
namespace MetricKMedian.Binary.Automatic.Poly
@[fun_prop] theorem int_mul : Poly (fun x : ℤ × ℤ => x.1*x.2) := ⟨PolyProgram.intMul⟩
end MetricKMedian.Binary.Automatic.Poly

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly
variable {α β A B : Type}

def prodData (x : Data A × Data B) : Data (A × B) :=
  ((x.1.1.1*x.2.1.1, x.1.1.2.flatMap (fun z => x.2.1.2.map (fun w => z*w))),
    x.1.2.flatMap (fun a => x.2.2.map (fun b => (a,b))))

 theorem prodData_raw (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (v : α → A) (w : β → B) :
    prodData (((raw μ).1,μ.states.toList.map v),((raw ν).1,ν.states.toList.map w)) =
      ((raw (μ.prod ν Prod.mk)).1,(μ.prod ν Prod.mk).states.toList.map (Prod.map v w)) := by
  simp only [prodData,raw,states_list,List.flatMap_def,List.map_ofFn,Function.comp_def,
    RoundingList.ofFn_product,SparseIntegerLaw.prod,Vector.toList_ofFn]
  rfl

@[fun_prop] theorem prodData_poly [Coding A] [Coding B] [Inhabited A] [Inhabited B] :
    Poly (prodData (A:=A) (B:=B)) := by
  unfold prodData
  apply pair
  · apply pair
    · fun_prop
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
