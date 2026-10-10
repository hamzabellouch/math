import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras
import OAI.Combinatorics.KMedian.Preparation.RepresentativeProgram
import OAI.Combinatorics.KMedian.Geometry.RationalUnitInput

namespace OAI


                                                 
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
abbrev Raw := (List ℚ × Table) × (List (List ℚ) × (List (List ℚ) × List (List ℚ)))
def view {f j : ℕ} (U : RationalUnitInput f j) : Raw :=
  ((List.ofFn U.y,List.ofFn (fun c => setView (U.F c))),
    (List.ofFn (fun c => List.ofFn (U.dc c)),(List.ofFn (fun c => List.ofFn (U.dd c)),List.ofFn (fun a => List.ofFn (U.df a)))))
structure Input where
  f : ℕ
  j : ℕ
  U : RationalUnitInput f j
abbrev Input.raw (x : Input) := view x.U
abbrev Input.encode (x : Input) := enc x.raw

def values (x : Raw) : List ℚ := (indices x.1.2).map (fun c =>
  ((indices x.1.1).map (fun a => if MetricKMedian.MaskProgram.get (x.1.2[c]?.getD []) a then
    x.1.1[a]?.getD 0*(x.2.1[c]?.getD [])[a]?.getD 0 else 0)).sum)
@[fun_prop] theorem values_poly : Poly values := by
  unfold values; apply list_map
  · apply comp rat_sum
    apply list_map <;> fun_prop
  · fun_prop
 theorem values_view {f j : ℕ} (U : RationalUnitInput f j) : values (view U)=List.ofFn U.V := by
  simp only [values,view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,decide_eq_true_eq,List.sum_ofFn,← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rfl

def Input.rep (M : ℚ) (x : Input) : RationalRepresentatives.Program.Input :=
  ⟨x.j,x.U.V,x.U.dd,M,univ⟩
def repData (M : ℚ) (x : Raw) : RationalRepresentatives.Program.Raw :=
  ((values x,(x.2.2.1,M)),x.1.2.map (fun _ => true))
@[fun_prop] theorem repData_poly (M : ℚ) : Poly (repData M) := by
  unfold repData
  have : Poly (fun x : Raw => x.1.2.map (fun _ => true)) := by apply list_map <;> fun_prop
  fun_prop
 theorem repData_view (M : ℚ) (x : Input) : repData M x.raw=(x.rep M).raw := by
  unfold repData
  rw [show values x.raw=List.ofFn x.U.V from values_view x.U]
  simp only [Input.rep,RationalRepresentatives.Program.Input.raw,Input.raw,view,setView,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact (decide_eq_true (Finset.mem_univ i)).symm

noncomputable def repInputProgram (M : ℚ) : PolyProgram Input.encode RationalRepresentatives.Program.Input.encode (Input.rep M) :=
  (repData_poly M).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (repData_view M x))
noncomputable def repProgram (M : ℚ) : PolyProgram Input.encode (enc : Row → List Bool)
    (fun x => setView (x.U.representatives M)) :=
  (repInputProgram M |>.comp RationalRepresentatives.Program.program).congr _ (fun _ => rfl)

def ranks (x : Row) : List ℕ := (indices x).filter (fun i => MetricKMedian.MaskProgram.get x i)
@[fun_prop] theorem ranks_poly : Poly ranks := by unfold ranks; apply list_filter <;> fun_prop
 theorem ranks_view {n : ℕ} (s : Finset (Fin n)) :
    ranks (setView s)=List.ofFn (fun i : Fin s.card => (s.orderEmbOfFin rfl i).val) := by
  have h : ((List.finRange n).filter (fun i => decide (i∈s))).map Fin.val =
      List.ofFn (fun i : Fin s.card => (s.orderEmbOfFin rfl i).val) := by
    rw [EncodingLists.filter_range,Finset.filter_mem_eq_inter,Finset.univ_inter,
      ← EncodingLists.sorted_enum,List.map_ofFn]
    rfl
  rw [← h]
  simp only [ranks,indices,setView,List.length_ofFn,RoundingList.range_finRange,List.filter_map]
  congr 1
  apply List.filter_congr
  intro i hi
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta]

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
