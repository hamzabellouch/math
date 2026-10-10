import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchActionArrays

namespace OAI


                                      
section
namespace MetricKMedian.RationalBatchData.GraphData
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch Finset
open SparseGraph.ListOperation (Row Table setView indices view)

def transpose (G : Table) : Table := (indices G).map (fun h => G.map (fun col => col[h]?.getD false))
def masses (x : ℚ × Table) : List ℚ := (transpose x.2).map (fun row => x.1*((row.filter id).length:ℚ))
def amount (m : List ℚ) : ℚ := (m.map (fun q => max (1-q) 0)).sum
def heavy (x : ℚ × List ℚ) : Row := x.2.map (fun q => decide (max 1 (x.1*amount x.2)<q))
abbrev Raw := ((ℚ × ℚ) × (ℕ × (ℚ × ℚ))) × Table
def prepare (x : Raw) : ActionArrays.Raw :=
  (((x.1.2.2,masses (x.1.1.1,x.2)),x.1.2.1),
    (transpose x.2,heavy (x.1.1.2,masses (x.1.1.1,x.2))))
def data (x : Raw) : SparsePhysicalBatch.ListOperation.Raw := ActionArrays.data (prepare x)

@[fun_prop] theorem transpose_poly : Poly transpose := by
  unfold transpose
  apply list_map
  · apply list_map <;> fun_prop
  · fun_prop
@[fun_prop] theorem masses_poly : Poly masses := by
  unfold masses
  apply list_map
  · have hf : Poly (fun x : (ℚ × Table) × Row => x.2.filter id) := by apply list_filter <;> fun_prop
    fun_prop
  · fun_prop
@[fun_prop] theorem amount_poly : Poly amount := by
  unfold amount
  apply comp rat_sum
  apply list_map <;> fun_prop
@[fun_prop] theorem heavy_poly : Poly heavy := by unfold heavy; apply list_map <;> fun_prop
@[fun_prop] theorem prepare_poly : Poly prepare := by unfold prepare; fun_prop
@[fun_prop] theorem data_poly : Poly data := by unfold data; fun_prop

 theorem transpose_view {n : ℕ} (G : Fin n → Finset (Fin n)) :
    transpose (view G)=List.ofFn (fun h => setView ((graph G).erase h)) := by
  simp only [transpose,indices,view,List.length_ofFn,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,Fin.eta,setView,graph,mem_filter,mem_univ,true_and]
 theorem masses_view {n : ℕ} (G : Fin n → Finset (Fin n)) (g : ℚ) :
    masses (g,view G)=List.ofFn (graphMass G g) := by
  simp only [masses,transpose_view,List.map_ofFn,Function.comp_def,setView,EncodingLists.bool_card]
  rfl
 theorem amount_view {n : ℕ} (m : Fin n → ℚ) : amount (List.ofFn m)=RationalBatchData.amount m := by
  simp only [amount,List.map_ofFn,List.sum_ofFn,Function.comp_def,RationalBatchData.amount]
 theorem heavy_view {n : ℕ} (m : Fin n → ℚ) (b : ℚ) :
    heavy (b,List.ofFn m)=setView (heavySet m b) := by
  simp only [heavy,amount_view,List.map_ofFn,Function.comp_def,setView,heavySet,mem_filter,mem_univ,true_and]
 theorem prepare_view {n : ℕ} (G : Fin n → Finset (Fin n)) (g b p φ : ℚ) (Δ : ℕ) :
    prepare (((g,b),(Δ,(p,φ))),view G)=
      ((((p,φ),List.ofFn (graphMass G g)),Δ),ActionList.view (graph G) (heavySet (graphMass G g) b)) := by
  simp only [prepare,masses_view,heavy_view,transpose_view,ActionList.view]
end MetricKMedian.RationalBatchData.GraphData
end

end OAI
