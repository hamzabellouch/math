import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalWeightedStep
import OAI.Combinatorics.KMedian.Binary.BinaryAutomatic
import OAI.Combinatorics.KMedian.Compression.GaussianListOperations
import OAI.Combinatorics.KMedian.Geometry.SortedListEncoding

namespace OAI


                                              
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset
abbrev Row := List ℚ
abbrev er := encodeList Ratio.encode

def frac (q : ℚ) : Bool := decide (0<q) && decide (q<1)
def indices (p : Row) : List ℕ := List.range p.length
def fractional (p : Row) : List ℕ := (indices p).filter (fun i => frac (p[i]?.getD 0))
def first (p : Row) : ℕ := (indices p).findIdx (fun i => frac (p[i]?.getD 0))
def second (p : Row) : ℕ := (indices p).findIdx (fun i => frac (p[i]?.getD 0) && decide (i≠first p))
def active (p : Row) : Bool := decide (1<(fractional p).length)
def ratio (β p : Row) : ℚ := β[first p]?.getD 0 / β[second p]?.getD 0

def up (p : Row) (i j : ℕ) (r : ℚ) := min (1-p[i]?.getD 0) (p[j]?.getD 0/r)
def down (p : Row) (i j : ℕ) (r : ℚ) := min (p[i]?.getD 0) ((1-p[j]?.getD 0)/r)
def move (p : Row) (i j : ℕ) (r t : ℚ) : Row :=
  (indices p).map (fun k => p[k]?.getD 0+t*((if k=i then 1 else 0)-(if k=j then r else 0)))
def probability (β p : Row) : ℚ :=
  if active p then
    down p (first p) (second p) (ratio β p) /
      (up p (first p) (second p) (ratio β p)+down p (first p) (second p) (ratio β p))
  else 0

def endpoint (β p : Row) (b : Bool) : Row :=
  if active p then move p (first p) (second p) (ratio β p)
    (if b then -down p (first p) (second p) (ratio β p) else up p (first p) (second p) (ratio β p))
  else p

theorem range_finRange (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_range,List.getElem_map,List.getElem_finRange,Fin.val_cast]

theorem fractional_list {n : ℕ} (p : Vector ℚ n) :
    fractional p.toList=((RationalWeightedStep.fractional p).sort).map Fin.val := by
  simp only [fractional,indices,Vector.length_toList,range_finRange,List.filter_map]
  unfold RationalWeightedStep.fractional
  rw [← EncodingLists.filter_range]
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro index _
  simp [frac, RationalWeightedStep.point]

theorem active_list {n : ℕ} (p : Vector ℚ n) :
    active p.toList=decide (1<(RationalWeightedStep.fractional p).card) := by
  simp only [active,fractional_list,List.length_map,Finset.length_sort]

theorem findIdx_min {n : ℕ} (s : Finset (Fin n)) (hs : s.Nonempty) (f : ℕ → Bool)
    (hf : ∀ i : Fin n, f i.val=decide (i∈s)) :
    (List.range n).findIdx f=(s.min' hs).val := by
  let i := s.min' hs
  apply (List.findIdx_eq (by simpa only [List.length_range] using i.isLt)).mpr
  constructor
  · simp only [List.getElem_range]
    rw [hf i,decide_eq_true_eq]
    exact min'_mem s hs
  · intro j hj
    simp only [List.getElem_range]
    rw [hf ⟨j,Nat.lt_trans hj i.isLt⟩,decide_eq_false_iff_not]
    intro hm
    exact (not_le_of_gt hj) (s.min'_le _ hm)

theorem first_list {n : ℕ} (p : Vector ℚ n) (h : 1<(RationalWeightedStep.fractional p).card) :
    first p.toList=(RationalWeightedStep.pair p h).val.1.val := by
  unfold first indices
  rw [Vector.length_toList]
  apply findIdx_min
  · exact card_pos.mp (by omega)
  intro i
  simp [frac,RationalWeightedStep.fractional,RationalWeightedStep.point]

theorem second_list {n : ℕ} (p : Vector ℚ n) (h : 1<(RationalWeightedStep.fractional p).card) :
    second p.toList=(RationalWeightedStep.pair p h).val.2.val := by
  unfold second indices
  rw [Vector.length_toList,first_list p h]
  apply findIdx_min
  · rw [← card_pos,card_erase_of_mem (min'_mem _ _)]
    omega
  intro i
  simp only [frac,Vector.getElem?_toList,Vector.getElem?_eq_getElem i.isLt,Option.getD_some,
    ← Bool.decide_and,Finset.mem_erase]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

  simp only [RationalWeightedStep.pair,Fin.val_ne_iff,RationalWeightedStep.fractional,mem_filter,mem_univ,true_and,point]
  exact and_comm

theorem get_point {n : ℕ} (p : Vector ℚ n) (i : Fin n) : p.toList[i.val]?.getD 0=point p i := by simp [point]
theorem up_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    up p.toList i.val j.val r=RationalWeightedStep.up p i j r := by simp only [up,RationalWeightedStep.up,get_point]
theorem down_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    down p.toList i.val j.val r=RationalWeightedStep.down p i j r := by simp only [down,RationalWeightedStep.down,get_point]
theorem move_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) :
    move p.toList i.val j.val r t=(RationalWeightedStep.move p i j r t).toList := by
  simp only [move,indices,Vector.length_toList,range_finRange,List.map_map,RationalWeightedStep.move,Vector.toList_ofFn,List.ofFn_eq_map]
  congr 1
  funext k
  simp only [Function.comp_def,get_point,Fin.val_inj]

theorem probability_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    probability (List.ofFn β) p.toList=RationalWeightedStep.probability β p := by
  unfold probability RationalWeightedStep.probability
  rw [active_list]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp only [ratio,first_list p h,second_list p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
  · rfl

theorem endpoint_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) :
    endpoint (List.ofFn β) p.toList (decide (b≠0))=(RationalWeightedStep.endpoint β p b).toList := by
  unfold endpoint RationalWeightedStep.endpoint
  rw [active_list]
  simp only [decide_eq_true_eq]
  by_cases h : 1<(RationalWeightedStep.fractional p).card
  · simp only [ite_eq_left h,dite_eq_left h,ratio,first_list p h,second_list p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
    by_cases hb : b=0 <;> simp [hb,move_list]
  · simp only [ite_eq_right h,dite_eq_right h]

@[fun_prop] theorem frac_poly : Poly frac := by unfold frac; fun_prop
@[fun_prop] theorem indices_poly : Poly indices := list_indices
@[fun_prop] theorem fractional_poly : Poly fractional := by
  unfold fractional
  apply list_filter <;> fun_prop
@[fun_prop] theorem first_poly : Poly first := by
  unfold first
  apply list_findIdx <;> fun_prop
@[fun_prop] theorem second_poly : Poly second := by
  unfold second
  apply list_findIdx
  · simp only [ne_eq,decide_not]
    fun_prop
  · fun_prop
@[fun_prop] theorem active_poly : Poly active := by unfold active; fun_prop
@[fun_prop] theorem ratio_poly : Poly (fun x : Row × Row => ratio x.1 x.2) := by unfold ratio; fun_prop
@[fun_prop] theorem up_poly : Poly (fun x : Row × (ℕ × (ℕ × ℚ)) => up x.1 x.2.1 x.2.2.1 x.2.2.2) := by unfold up; fun_prop
@[fun_prop] theorem down_poly : Poly (fun x : Row × (ℕ × (ℕ × ℚ)) => down x.1 x.2.1 x.2.2.1 x.2.2.2) := by unfold down; fun_prop
@[fun_prop] theorem move_poly : Poly (fun x : Row × (ℕ × (ℕ × (ℚ × ℚ))) => move x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold move
  apply list_map
  · fun_prop
  · fun_prop
@[fun_prop] theorem probability_poly : Poly (fun x : Row × Row => probability x.1 x.2) := by unfold probability; fun_prop
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (fun x : Row × Row => endpoint x.1 x.2 b) := by
  unfold endpoint
  cases b <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> fun_prop

end MetricKMedian.RoundingList
end

end OAI
