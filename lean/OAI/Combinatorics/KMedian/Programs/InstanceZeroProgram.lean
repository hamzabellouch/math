import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ZeroCostBranch
import OAI.Combinatorics.KMedian.Programs.MaskBestProgram
import OAI.Combinatorics.KMedian.Programs.InstanceDataProgram

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
open Completion.Rational.BestProgram (card card_view)
def subsetRaw (x : Row × Row) : Bool := (x.1.zip x.2).all (fun p => !p.1 || p.2)
@[fun_prop] theorem subsetRaw_poly : Poly subsetRaw := by
  unfold subsetRaw
  have h : Poly (fun x : Row × Row => (x.1.zip x.2).map (fun p => !p.1 || p.2)) := by apply list_map <;> fun_prop
  simpa only [List.all_map,Function.comp_def,id_eq] using (comp bool_all h)
 theorem subsetRaw_view {n : ℕ} (S T : Finset (Fin n)) : subsetRaw (setView S,setView T)=decide (S⊆T) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subsetRaw,setView,Gaussian.ListOperation.zip_ofFn,List.all_eq_true,List.mem_ofFn,Bool.or_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_true_eq]
  constructor
  · intro h i hi
    have hh : i∉S ∨ i∈T := by simpa only [decide_eq_false_iff_not,decide_eq_true_eq] using h _ ⟨i,rfl⟩
    exact hh.resolve_left (not_not_intro hi)
  · intro h z hz
    obtain ⟨i,rfl⟩ := hz
    by_cases hi : i∈S
    · exact Or.inr (by simpa only [decide_eq_true_eq] using h hi)
    · exact Or.inl (by simpa only [decide_eq_false_iff_not] using hi)

def zeroTestData (x : Raw) : Bool := subsetRaw x.1 && decide (card x.1.1≤x.2.1)
@[fun_prop] theorem zeroTestData_poly : Poly zeroTestData := by unfold zeroTestData; fun_prop
 theorem zeroTestData_view (I : Instance) : zeroTestData (view I)=decide I.zeroTest := by
  apply Bool.eq_iff_iff.mpr
  simp only [zeroTestData,view,subsetRaw_view,card_view,Bool.and_eq_true,decide_eq_true_eq]
  rfl
noncomputable def zeroTestProgram : PolyProgram encode encodeBool (fun I => decide I.zeroTest) :=
  zeroTestData_poly.program.recode view (fun _ => rfl) (fun I => congrArg encodeBool (zeroTestData_view I))

def first (O : Row) : ℕ := O.findIdx id
@[fun_prop] theorem first_poly : Poly first := by unfold first; apply list_findIdx <;> fun_prop
 theorem first_view {n : ℕ} (O : Finset (Fin n)) (hO : O.Nonempty) : first (setView O)=(O.min' hO).val := by
  unfold first
  apply (List.findIdx_eq (by simp only [setView,List.length_ofFn]; exact (O.min' hO).isLt)).mpr
  constructor
  · simp only [setView,List.getElem_ofFn,id_eq,Fin.eta,decide_eq_true_eq]; exact min'_mem _ _
  · intro k hk
    have hkn : k<n := hk.trans (O.min' hO).isLt
    simp only [setView,List.getElem_ofFn,id_eq,decide_eq_false_iff_not]
    intro hm
    exact (not_le_of_gt hk) (O.min'_le ⟨k,hkn⟩ hm)
def singletonRaw (x : Row × ℕ) : Row := (indices x.1).map (fun i => decide (i=x.2))
@[fun_prop] theorem singletonRaw_poly : Poly singletonRaw := by unfold singletonRaw; apply list_map <;> fun_prop
 theorem singletonRaw_view {n : ℕ} (S : Finset (Fin n)) (a : Fin n) : singletonRaw (setView S,a.val)=setView {a} := by
  simp only [singletonRaw,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,mem_singleton,Fin.ext_iff]
def singletonData (x : Raw) : Row := singletonRaw (x.1.2,first x.1.2)
@[fun_prop] theorem singletonData_poly : Poly singletonData := by unfold singletonData; fun_prop
 theorem singletonData_view (I : Instance) : singletonData (view I)=setView {I.facilities.min' I.facilities_nonempty} := by
  unfold singletonData view
  rw [first_view,singletonRaw_view]
def zeroOutputData (x : Raw) : Row := if x.1.1.any id then x.1.1 else singletonData x
@[fun_prop] theorem zeroOutputData_poly : Poly zeroOutputData := by unfold zeroOutputData; fun_prop
 theorem zeroOutputData_view (I : Instance) : zeroOutputData (view I)=setView I.zeroOutput := by
  unfold zeroOutputData Instance.zeroOutput
  change (if (setView I.clients).any id then setView I.clients else singletonData (view I))=_
  rw [Completion.Rational.PackingProgram.any_view]
  simp only [decide_eq_true_eq]
  split_ifs
  · rfl
  · exact singletonData_view I
noncomputable def zeroOutputProgram : PolyProgram encode (enc : Row → List Bool) (fun I => setView I.zeroOutput) :=
  zeroOutputData_poly.program.recode view (fun _ => rfl) (fun I => congrArg enc (zeroOutputData_view I))
end MetricKMedian.InstanceProgram
end

end OAI
