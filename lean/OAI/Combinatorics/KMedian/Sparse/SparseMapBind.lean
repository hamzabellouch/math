import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMap
import OAI.Combinatorics.KMedian.Sparse.SparseBind

namespace OAI


                                     
section
namespace MetricKMedian.SparseIntegerLaw
variable {α β γ : Type}
 theorem map_map (μ : SparseIntegerLaw α) (f : α → β) (g : β → γ) :
    (μ.map f).map g=μ.map (g ∘ f) := by
  unfold map
  simp only [Vector.map_map]
 theorem map_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β) (f : β → γ) :
    (μ.bindIndexed κ).map f=μ.bindIndexed (fun i => (κ i).map f) := by
  unfold map bindIndexed
  congr 1
  ext i hi
  simp only [Vector.getElem_map,Vector.getElem_ofFn]
end MetricKMedian.SparseIntegerLaw
end

end OAI
