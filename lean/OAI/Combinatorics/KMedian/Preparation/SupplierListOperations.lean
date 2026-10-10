import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras
import OAI.Combinatorics.KMedian.Geometry.GraphListOperations
import OAI.Combinatorics.KMedian.Preparation.RationalSupplierScan

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
abbrev QRow := List ℚ
abbrev BTable := List (List Bool)
abbrev SupplierRaw := QRow × (BTable × (BTable × (QRow × (QRow × ℚ))))
def supplierView {f n : ℕ} (S : Data f n) : SupplierRaw :=
  (List.ofFn S.y,(List.ofFn (fun t => setView (S.P t)),(List.ofFn (fun t => setView (S.A t)),
    (List.ofFn S.p,(List.ofFn S.c,S.γ)))))

theorem ofFn_sum {m n : ℕ} {α : Type} (F : Fin m ⊕ Fin n → α) :
    List.ofFn (fun i => F (finSumFinEquiv.symm i)) =
    List.ofFn (fun i => F (.inl i)) ++ List.ofFn (fun i => F (.inr i)) := by
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem finSum_symm_castLE {m n : ℕ} (h : m ≤ m+n) (i : Fin m) :
    (finSumFinEquiv.symm (Fin.castLE h i) : Fin m ⊕ Fin n)=.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

theorem append_poly {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x++g x) :=
  comp list_append (pair hf hg)

theorem ofFn_star {f n : ℕ} {α : Type} (F : SupplierStars.Star (Fin f) (Fin n) → α) :
    List.ofFn (fun i => F (index i)) =
    List.ofFn (fun i => F (.inl i)) ++
      ((List.ofFn (fun s => List.ofFn (fun t => F (.inr (.inl (s,t)))))).flatten ++
        List.ofFn (fun t => F (.inr (.inr t)))) := by
  conv_lhs => rw [List.ofFn_add]
  simp only [index,Equiv.trans_apply,Equiv.sumCongr_apply,finSum_symm_castLE,
    finSumFinEquiv_symm_apply_natAdd,Sum.map_inl,Sum.map_inr,Equiv.refl_apply]
  conv_lhs => arg 2; rw [List.ofFn_add]
  simp only [finSum_symm_castLE,
    finSumFinEquiv_symm_apply_natAdd,Sum.map_inl,Sum.map_inr,Equiv.refl_apply]
  rw [RoundingList.ofFn_product]

def targetsData (x : SupplierRaw) : BTable :=
  ((indices x.1).map (fun i => (indices x.2.2.2.1).map (fun t => (x.2.2.1[t]?.getD [])[i]?.getD false))) ++
  (((indices x.2.2.2.1).flatMap (fun s => (indices x.2.2.2.1).map (fun _ =>
    (indices x.2.2.2.1).map (fun j => decide (j=s))))) ++
    (indices x.2.2.2.1).map (fun t => (indices x.2.2.2.1).map (fun j => decide (j=t))))
@[fun_prop] theorem targetsData_poly : Poly targetsData := by
  unfold targetsData
  apply append_poly
  · apply list_map <;> (first | (apply list_map <;> fun_prop) | fun_prop)
  · apply append_poly
    · apply list_flatMap
      · apply list_map
        · apply list_map <;> fun_prop
        · fun_prop
      · fun_prop
    · apply list_map
      · apply list_map <;> fun_prop
      · fun_prop

def flagsData (x : SupplierRaw) : QRow := x.1.map (fun _ => 1) ++
  (x.2.2.2.1.flatMap (fun _ => x.2.2.2.1.map (fun _ => 0)) ++ x.2.2.2.1.map (fun _ => 0))
@[fun_prop] theorem flagsData_poly : Poly flagsData := by
  unfold flagsData
  apply append_poly
  · apply list_map <;> fun_prop
  · apply append_poly
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
    · apply list_map <;> fun_prop

def outsideData (x : SupplierRaw) (i : ℕ) : Bool := (x.2.1.map (fun P => !(P[i]?.getD false))).all id
def pairWeight (x : SupplierRaw) (s t : ℕ) : ℚ :=
  ((indices x.1).map (fun i => if ((x.2.2.1[s]?.getD [])[i]?.getD false) &&
    ((x.2.1[t]?.getD [])[i]?.getD false) then x.1[i]?.getD 0 else 0)).sum
def weightsData (x : SupplierRaw) : QRow :=
  ((indices x.1).map (fun i => if outsideData x i then x.1[i]?.getD 0 else 0)) ++
  (((indices x.2.2.2.1).flatMap (fun s => (indices x.2.2.2.1).map (fun t => pairWeight x s t))) ++
    x.2.2.2.2.1.map (fun c => x.2.2.2.2.2*c))
@[fun_prop] theorem outsideData_poly : Poly (fun x : SupplierRaw × ℕ => outsideData x.1 x.2) := by
  unfold outsideData; apply comp bool_all; apply list_map <;> fun_prop
@[fun_prop] theorem pairWeight_poly : Poly (fun x : SupplierRaw × (ℕ × ℕ) => pairWeight x.1 x.2.1 x.2.2) := by
  unfold pairWeight; apply comp rat_sum; apply list_map <;> fun_prop
@[fun_prop] theorem weightsData_poly : Poly weightsData := by
  unfold weightsData; apply append_poly
  · apply list_map <;> fun_prop
  · apply append_poly
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
    · apply list_map <;> fun_prop

 theorem targetsData_view {f n : ℕ} (S : Data f n) :
    targetsData (supplierView S)=List.ofFn (fun e => setView (D S.A e)) := by
  rw [show (fun e => setView (D S.A e))=(fun e => setView (SupplierStars.targets S.A (index e))) by rfl,ofFn_star (fun e => setView (SupplierStars.targets S.A e))]
  simp only [targetsData,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    List.flatMap_def,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,SupplierStars.targets,
    setView,mem_filter,mem_univ,true_and,mem_singleton]
  simp only [Fin.val_inj]

 theorem flagsData_view {f n : ℕ} (S : Data f n) : flagsData (supplierView S)=List.ofFn (a (f:=f) (n:=n)) := by
  change _=List.ofFn (fun e => flagQ (index e))
  rw [ofFn_star]
  simp only [flagsData,supplierView,List.flatMap_def,List.map_ofFn,Function.comp_def,flagQ]

 theorem outsideData_view {f n : ℕ} (S : Data f n) (i : Fin f) :
    outsideData (supplierView S) i.val=decide (i∈SupplierStars.outside S.P) := by
  apply Bool.eq_iff_iff.mpr
  simp only [outsideData,supplierView,List.all_map,Function.comp_def,id_eq,List.all_eq_true,List.mem_ofFn,
    forall_exists_index,forall_apply_eq_imp_iff,setView,List.getElem?_ofFn,dite_eq_left i.isLt,
    Option.getD_some,Fin.eta,decide_eq_true_eq,SupplierStars.outside,
    mem_filter,mem_univ,true_and]
  simp

 theorem pairWeight_view {f n : ℕ} (S : Data f n) (s t : Fin n) :
    pairWeight (supplierView S) s.val t.val=∑ i∈S.A s∩S.P t,S.y i := by
  simp only [pairWeight,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,setView,Fin.eta,← Bool.decide_and,decide_eq_true_eq,List.sum_ofFn]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

 theorem weightsData_view {f n : ℕ} (S : Data f n) :
    weightsData (supplierView S)=List.ofFn (fun e => weightQ S.y S.P S.A S.c S.γ (index e)) := by
  rw [ofFn_star]
  simp only [weightsData,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    List.flatMap_def,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  change (List.ofFn (fun i => if outsideData (supplierView S) i.val then S.y i else 0) ++
     ((List.ofFn (fun s => List.ofFn (fun t => pairWeight (supplierView S) s.val t.val))).flatten ++
       List.ofFn (fun t => S.γ*S.c t)))=_
  simp only [outsideData_view,pairWeight_view,decide_eq_true_eq,weightQ]
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
