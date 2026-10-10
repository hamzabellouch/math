import Mathlib
import OAI.Combinatorics.KMedian.Model
import OAI.Combinatorics.KMedian.Binary.BinaryAutoFiniteLists
import OAI.Combinatorics.KMedian.Geometry.GraphListOperations

namespace OAI


                                         
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)

abbrev get (r : Row) (i : ℕ) : Bool := r[i]?.getD false
@[simp] theorem get_view {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : get (setView s) i=decide (i∈s) := by
  simp only [get,setView,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta]

def intersect (x : Row × Row) : Bool := (x.1.zip x.2).any (fun z => z.1 && z.2)
@[fun_prop] theorem intersect_poly : Poly intersect := by
  unfold intersect
  have h : Poly (fun x : Row × Row => (x.1.zip x.2).map (fun z => z.1 && z.2)) := by
    apply list_map <;> fun_prop
  simpa only [List.any_map,Function.comp_def,id_eq] using (comp bool_any h)
 theorem intersect_view {n : ℕ} (s t : Finset (Fin n)) : intersect (setView s,setView t)=decide (¬Disjoint s t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [intersect,setView,Gaussian.ListOperation.zip_ofFn,List.any_eq_true,List.mem_ofFn,
    Bool.and_eq_true,decide_eq_true_eq,Finset.not_disjoint_iff]
  constructor
  · rintro ⟨z,⟨i,rfl⟩,hs,ht⟩
    exact ⟨i,of_decide_eq_true hs,of_decide_eq_true ht⟩
  · rintro ⟨i,hs,ht⟩
    exact ⟨_,⟨i,rfl⟩,decide_eq_true hs,decide_eq_true ht⟩

def selectedValues (x : List ℚ × Row) : List ℚ :=
  ((indices x.2).filter (fun i => get x.2 i)).map (fun i => x.1[i]?.getD 0)
def nearest (x : List ℚ × Row) : ℕ :=
  (indices x.2).findIdx (fun i => get x.2 i && decide (x.1[i]?.getD 0=LPBinary.minimum (selectedValues x)))
@[fun_prop] theorem selectedValues_poly : Poly selectedValues := by
  unfold selectedValues
  apply list_map
  · fun_prop
  · apply list_filter <;> fun_prop
@[fun_prop] theorem nearest_poly : Poly nearest := by
  unfold nearest
  have hm : Poly LPBinary.minimum := ⟨LPBinary.Program.minimumProgram⟩
  apply list_findIdx <;> fun_prop
 theorem selectedValues_mem {n : ℕ} (R : Fin n → ℚ) (U : Finset (Fin n)) (q : ℚ) :
    q∈selectedValues (List.ofFn R,setView U) ↔ q∈U.image R := by
  simp only [selectedValues,indices,setView,List.length_ofFn,List.mem_map,List.mem_filter,List.mem_range,mem_image]
  constructor
  · rintro ⟨i,⟨hi,hu⟩,he⟩
    have hu' : (⟨i,hi⟩ : Fin n)∈U := by
      simpa only [get,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some,decide_eq_true_eq] using hu
    have he' : R ⟨i,hi⟩=q := by simpa only [List.getElem?_ofFn,dite_eq_left hi,Option.getD_some] using he
    exact ⟨⟨i,hi⟩,hu',he'⟩
  · rintro ⟨i,hi,rfl⟩
    refine ⟨i.val,⟨i.isLt,?_⟩,?_⟩
    · simpa only [get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true_eq] using hi
    · simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta]
 theorem nearest_view {n : ℕ} (R : Fin n → ℚ) (U : Finset (Fin n)) (hU : U.Nonempty) :
    nearest (List.ofFn R,setView U)=(Preparation.firstNearest U R hU).val := by
  let a := Preparation.firstNearest U R hU
  have hm : LPBinary.minimum (selectedValues (List.ofFn R,setView U))=R a :=
    (LPBinary.minimum_eq_finset _ _ (hU.image _) (selectedValues_mem R U)).trans
      (LPBinary.firstNearest_value U R hU).symm
  unfold nearest
  dsimp only
  unfold indices
  rw [show (setView U).length=n from by simp only [setView,List.length_ofFn]]
  change (List.range n).findIdx (fun i => get (setView U) i &&
    decide ((List.ofFn R)[i]?.getD 0=LPBinary.minimum (selectedValues (List.ofFn R,setView U))))=a.val
  rw [hm]
  apply (List.findIdx_eq (by simpa only [List.length_range] using a.isLt)).mpr
  refine ⟨?_,?_⟩
  · simp only [List.getElem_range,get,setView,List.getElem?_ofFn,dite_eq_left a.isLt,Option.getD_some,Fin.eta,
      decide_true,Bool.and_true,decide_eq_true_eq]
    exact (Preparation.firstNearest_spec U R hU).1
  · intro k hk
    have hkn : k<n := hk.trans a.isLt
    simp only [List.getElem_range,get,setView,List.getElem?_ofFn,dite_eq_left hkn,Option.getD_some]
    apply Bool.eq_false_iff.mpr
    intro h
    have hh : decide ((⟨k,hkn⟩ : Fin n)∈U)=true ∧ decide (R ⟨k,hkn⟩=R a)=true := by simpa only [Bool.and_eq_true] using h
    have hle := LPBinary.firstNearest_le U R hU ⟨k,hkn⟩ (of_decide_eq_true hh.1) (of_decide_eq_true hh.2)
    exact (not_le_of_gt hk) hle
end MetricKMedian.MaskProgram
end

end OAI
