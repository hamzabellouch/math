import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalSignedStep
import OAI.Combinatorics.KMedian.Process.RoundingListOperations

namespace OAI


                                            
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset

def square (p : Row) : List (ℕ × ℕ) := (indices p).flatMap (fun i => (indices p).map (fun j => (i,j)))

theorem square_poly : Poly square := by
  unfold square
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop
attribute [fun_prop] square_poly

theorem ofFn_product {m n : ℕ} {α : Type} (f : Fin m → Fin n → α) :
    (List.ofFn (fun i => (List.ofFn (f i)))).flatten=
      List.ofFn (fun z : Fin (m*n) => f (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  have bound (j : Fin n) : i.val*n+j.val < m*n := by
    have hh := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr i.isLt)
    simp only [Nat.succ_mul] at hh
    omega
  have he (j : Fin n) : (finProdFinEquiv.symm ⟨i.val*n+j.val,bound j⟩ : Fin m × Fin n)=(i,j) := by
    have hh : (⟨i.val*n+j.val,bound j⟩ : Fin (m*n))=finProdFinEquiv (i,j) := by
      apply Fin.ext
      change i.val*n+j.val=j.val+n*i.val
      ring
    rw [hh]
    exact finProdFinEquiv.symm_apply_apply (i,j)
  exact congrArg List.ofFn (funext (he · |> congrArg (fun z => f z.1 z.2))) |>.symm

theorem square_list {n : ℕ} (p : Vector ℚ n) :
    square p.toList=List.ofFn (fun z : Fin (n*n) => ((finProdFinEquiv.symm z).1.val,(finProdFinEquiv.symm z).2.val)) := by
  simp only [square,indices,Vector.length_toList,range_finRange,List.flatMap_def,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map]
  conv => lhs; arg 1; arg 1; intro i; rw [← List.ofFn_eq_map]
  exact ofFn_product _

namespace Signed

def valid (β p : Row) (ij : ℕ × ℕ) : Bool :=
  frac (p[ij.1]?.getD 0) && frac (p[ij.2]?.getD 0) &&
    decide (ij.1≠ij.2) && decide (0<β[ij.1]?.getD 0*β[ij.2]?.getD 0)
def index (β p : Row) : ℕ := (square p).findIdx (valid β p)
def pair (β p : Row) : ℕ × ℕ := (square p)[index β p]?.getD (0,0)
def active (β p : Row) : Bool := decide (index β p<(square p).length)
def ratio (β p : Row) : ℚ := β[(pair β p).1]?.getD 0/β[(pair β p).2]?.getD 0

def probability (β p : Row) : ℚ :=
  if active β p then
    down p (pair β p).1 (pair β p).2 (ratio β p) /
      (up p (pair β p).1 (pair β p).2 (ratio β p)+down p (pair β p).1 (pair β p).2 (ratio β p))
  else 0

def endpoint (β p : Row) (b : Bool) : Row :=
  if active β p then move p (pair β p).1 (pair β p).2 (ratio β p)
    (if b then -down p (pair β p).1 (pair β p).2 (ratio β p) else up p (pair β p).1 (pair β p).2 (ratio β p))
  else p

theorem valid_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (z : Fin (n*n)) :
    valid (List.ofFn β) p.toList ((finProdFinEquiv.symm z).1.val,(finProdFinEquiv.symm z).2.val)=
      decide (z∈RationalSignedStep.pairs β p) := by
  simp only [valid,frac,get_point,Gaussian.ListOperation.get_ofFn,← Bool.decide_and]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,RationalSignedStep.pairs,mem_filter,mem_univ,true_and,RationalWeightedStep.fractional,Fin.val_ne_iff]
  tauto

theorem active_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    active (List.ofFn β) p.toList=decide (RationalSignedStep.Active β p) := by
  unfold active index
  rw [square_list]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.findIdx_lt_length,List.mem_ofFn]
  constructor
  · rintro ⟨a,⟨z,rfl⟩,hz⟩
    exact ⟨z,by simpa only [valid_list,decide_eq_true_eq] using hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨_,⟨z,rfl⟩,by simpa only [valid_list,decide_eq_true_eq] using hz⟩

theorem index_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (h : RationalSignedStep.Active β p) :
    index (List.ofFn β) p.toList=((RationalSignedStep.pairs β p).min' h).val := by
  unfold index
  rw [square_list]
  let z := (RationalSignedStep.pairs β p).min' h
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using z.isLt)).mpr
  constructor
  · simp only [List.getElem_ofFn,valid_list,decide_eq_true_eq]
    exact min'_mem _ h
  · intro j hj
    simp only [List.getElem_ofFn,valid_list,decide_eq_false_iff_not]
    intro hm
    exact (not_le_of_gt hj) ((RationalSignedStep.pairs β p).min'_le _ hm)

theorem pair_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (h : RationalSignedStep.Active β p) :
    pair (List.ofFn β) p.toList=((RationalSignedStep.pair β p h).val.1.val,(RationalSignedStep.pair β p h).val.2.val) := by
  simp only [pair,index_list β p h,square_list,Gaussian.ListOperation.get_ofFn,RationalSignedStep.pair]

theorem probability_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    probability (List.ofFn β) p.toList=RationalSignedStep.probability β p := by
  unfold probability RationalSignedStep.probability
  rw [active_list]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp only [ratio,pair_list β p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
  · rfl

theorem endpoint_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) :
    endpoint (List.ofFn β) p.toList (decide (b≠0))=(RationalSignedStep.endpoint β p b).toList := by
  unfold endpoint RationalSignedStep.endpoint
  rw [active_list]
  simp only [decide_eq_true_eq]
  by_cases h : RationalSignedStep.Active β p
  · simp only [ite_eq_left h,dite_eq_left h,ratio,pair_list β p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
    by_cases hb : b=0 <;> simp [hb,move_list]
  · simp only [ite_eq_right h,dite_eq_right h]

@[fun_prop] theorem valid_poly : Poly (fun x : (Row × Row) × (ℕ × ℕ) => valid x.1.1 x.1.2 x.2) := by
  unfold valid
  simp only [ne_eq,decide_not]
  fun_prop
@[fun_prop] theorem index_poly : Poly (fun x : Row × Row => index x.1 x.2) := by
  unfold index
  apply list_findIdx <;> fun_prop
@[fun_prop] theorem pair_poly : Poly (fun x : Row × Row => pair x.1 x.2) := by unfold pair; fun_prop
@[fun_prop] theorem active_poly : Poly (fun x : Row × Row => active x.1 x.2) := by unfold active; fun_prop
@[fun_prop] theorem ratio_poly : Poly (fun x : Row × Row => ratio x.1 x.2) := by unfold ratio; fun_prop
@[fun_prop] theorem probability_poly : Poly (fun x : Row × Row => probability x.1 x.2) := by unfold probability; fun_prop
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (fun x : Row × Row => endpoint x.1 x.2 b) := by
  unfold endpoint
  cases b <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> fun_prop

end Signed
end MetricKMedian.RoundingList
end

end OAI
