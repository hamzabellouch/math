import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMarginalTools
import OAI.Combinatorics.KMedian.Sparse.SparseBindProgram

namespace OAI


                                   
section
namespace MetricKMedian.Binary
 theorem encodeList_map {α β : Type} (e : β → List Bool) (f : α → β) (xs : List α) :
    encodeList e (xs.map f)=encodeList (e ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,encodeList,ih,Function.comp_def]
end MetricKMedian.Binary

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
variable {α β A : Type}
def table (μ : SparseIntegerLaw α) (v : α → A) : Data A := ((raw μ).1,μ.states.toList.map v)
 theorem table_map (μ : SparseIntegerLaw α) (f : α → β) (v : β → A) :
    table (μ.map f) v=table μ (v ∘ f) := by
  simp only [table,raw,map,Vector.toList_map,List.map_map]

 theorem table_bind (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β) (v : β → A) :
    table (μ.bindIndexed κ) v=bindData ((raw μ).1,List.ofFn (fun i => table (κ i) v)) :=
  (bindData_raw μ κ v).symm

 theorem table_dirac (a : α) (v : α → A) : table (SparseIntegerLaw.dirac a) v=((1,[1]),[v a]) := by rfl

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
