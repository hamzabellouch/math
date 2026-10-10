import Mathlib
import OAI.Probability.Contingency.GreedyTable

namespace OAI

/-! Direct Cases. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

def DirectCase (_c : Fin n → ℕ) : Prop := m=0 ∨ n=0 ∨ (∑ i,r i)=0 ∨ m=1 ∨ n=1

theorem table_subsingleton_of_direct (h : DirectCase r c) : Subsingleton (Tables r c) := by
  constructor
  intro X Y
  apply Subtype.ext
  funext i j
  rcases h with hm | hn | hN | hm | hn
  · exact Fin.elim0 (hm ▸ i)
  · exact Fin.elim0 (hn ▸ j)
  · have hi : r i=0 := by
      have hh := Finset.single_le_sum (fun i _ => Nat.zero_le (r i)) (Finset.mem_univ i)
      omega
    have hx := Finset.single_le_sum (fun j _ => Nat.zero_le (X.val i j)) (Finset.mem_univ j)
    have hy := Finset.single_le_sum (fun j _ => Nat.zero_le (Y.val i j)) (Finset.mem_univ j)
    rw [X.property.1 i,hi] at hx
    rw [Y.property.1 i,hi] at hy
    omega
  · subst m
    have hx := X.property.2 j
    have hy := Y.property.2 j
    simp only [Fin.sum_univ_one] at hx hy
    have hi : i=0 := Fin.eq_zero i
    simp only [hi,hx,hy]
  · subst n
    have hx := X.property.1 i
    have hy := Y.property.1 i
    simp only [Fin.sum_univ_one] at hx hy
    have hj : j=0 := Fin.eq_zero j
    simp only [hj,hx,hy]

namespace Law
variable {α : Type*} [Fintype α] [Nonempty α] [Subsingleton α]

theorem uniform_subsingleton (x : α) : uniform α=pure x := by
  classical
  apply Law.ext
  funext a
  have hcard : Fintype.card α=1 := by rw [← Nat.card_eq_fintype_card]; exact Nat.card_unique
  simp [uniform,pure,hcard,Subsingleton.elim a x]

end Law

local instance directCasesTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

 

def arbitraryDraw (hrc : (∑ i,r i)=∑ j,c j) (k : ℕ) : DyadicLaw (Tables r c) := by
  classical
  by_cases h : DirectCase r c
  · exact DyadicLaw.pure (greedyTable r c hrc) 0
  · have hm : 0 < m := by by_contra hh; exact h (Or.inl (by omega))
    have hn : 0 < n := by by_contra hh; exact h (Or.inr (Or.inl (by omega)))
    exact PaddedGraph.canonicalDraw r c hm hn hrc k

theorem arbitraryDraw_bits (hrc : (∑ i,r i)=∑ j,c j) (k : ℕ) :
    (arbitraryDraw r c hrc k).bits≤Schedule.R (Parameters.dim m n) (Parameters.bits m n (∑ i,r i)) k := by
  classical
  unfold arbitraryDraw
  split_ifs
  · exact Nat.zero_le _
  · exact (PaddedGraph.canonicalDraw_bits _ _ _ _ _ _).le

 

theorem arbitraryDraw_tv (hrc : (∑ i,r i)=∑ j,c j) (k : ℕ) (hk : 1≤k) :
    letI := tables_nonempty r c hrc
    (arbitraryDraw r c hrc k).toLaw.tv (Law.uniform (Tables r c))≤(2:ℝ)^(-(k:ℤ)) := by
  classical
  let := tables_nonempty r c hrc
  unfold arbitraryDraw
  split_ifs with h
  · have huni : Law.uniform (Tables r c)=Law.pure (greedyTable r c hrc) := by
      let := table_subsingleton_of_direct r c h
      exact Law.uniform_subsingleton _
    rw [DyadicLaw.toLaw_pure,huni,Law.tv_self]
    positivity
  · exact PaddedGraph.canonicalDraw_tv _ _ _ _ _ _ hk

end
end Contingency

 

 

open scoped BigOperators
namespace Contingency.IntegerTabulation

 

def step {s : ℕ} (A : Fin s → Fin s → ℕ) (v : Fin s → ℕ) (j : Fin s) : ℕ :=
  ∑ i,v i*A i j

def propagate {s : ℕ} (A : Fin s → Fin s → ℕ) (v : Fin s → ℕ) : ℕ → (Fin s → ℕ)
  | 0 => v
  | t+1 => step A (propagate A v t)

 

def propagationOps (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => propagationOps s t+2*s*s

theorem propagationOps_eq (s t : ℕ) : propagationOps s t=2*t*s^2 := by
  induction t with
  | zero => simp [propagationOps]
  | succ t ih => rw [propagationOps,ih]; ring

theorem step_total {s : ℕ} (A : Fin s → Fin s → ℕ) (v : Fin s → ℕ) (Q : ℕ)
    (hA : ∀ i,∑ j,A i j=2^Q) : (∑ j,step A v j)=(∑ i,v i)*2^Q := by
  unfold step
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hA]
  rw [Finset.sum_mul]

theorem propagate_total {s : ℕ} (A : Fin s → Fin s → ℕ) (v : Fin s → ℕ) (Q R : ℕ)
    (hA : ∀ i,∑ j,A i j=2^Q) (hv : ∑ i,v i=2^R) (t : ℕ) :
    (∑ i,propagate A v t i)=2^(R+t*Q) := by
  induction t with
  | zero => simpa [propagate] using hv
  | succ t ih => rw [propagate,step_total _ _ Q hA,ih,← pow_add]; congr 1; ring

theorem propagate_entry_bound {s : ℕ} (A : Fin s → Fin s → ℕ) (v : Fin s → ℕ) (Q R : ℕ)
    (hA : ∀ i,∑ j,A i j=2^Q) (hv : ∑ i,v i=2^R) (t : ℕ) (i : Fin s) :
    propagate A v t i≤2^(R+t*Q) := by
  rw [← propagate_total A v Q R hA hv t]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

 

theorem partial_step_bound {s : ℕ} (A : Fin s → Fin s → ℕ) (v : Fin s → ℕ) (Q R : ℕ)
    (hA : ∀ i,∑ j,A i j=2^Q) (hv : ∑ i,v i=2^R) (t : ℕ) (j : Fin s) (I : Finset (Fin s)) :
    (∑ i∈I,propagate A v t i*A i j)≤2^(R+(t+1)*Q) := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun _ _ _ => Nat.zero_le _)).trans
  exact propagate_entry_bound A v Q R hA hv (t+1) j

 

theorem propagate_walk {s : ℕ} (q : Fin s → DyadicLaw (Fin s)) (Q : ℕ)
    (hq : ∀ i,(q i).bits=Q) (i₀ : Fin s) (t : ℕ) :
    propagate (fun i j => (q i).count j) (fun i => if i=i₀ then 1 else 0) t=
      (DyadicLaw.walk q Q hq i₀ t).count := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    simp only [propagate,step,DyadicLaw.walk,DyadicLaw.bind,ih]

 

def stoppedVector {s : ℕ} (R φ : ℕ) (a : Fin s → ℕ) (z₀ : Fin s) : ℕ → (Fin s → ℕ)
  | 0 => fun z => if z=z₀ then 1 else 0
  | j+1 => fun z => a z*2^(R*j)+φ*stoppedVector R φ a z₀ j z

theorem stoppedVector_eq {s : ℕ} (R φ : ℕ) (a : Fin s → ℕ) (z₀ : Fin s) (J : ℕ) (z : Fin s) :
    stoppedVector R φ a z₀ J z=stoppedNumerator R φ a z₀ z J := by
  induction J with
  | zero => rfl
  | succ J ih => simp only [stoppedVector,stoppedNumerator,ih]

theorem stoppedVector_total {s : ℕ} (R φ : ℕ) (a : Fin s → ℕ) (z₀ : Fin s)
    (ht : (∑ z,a z)+φ=2^R) (J : ℕ) : (∑ z,stoppedVector R φ a z₀ J z)=2^(R*J) := by
  simp_rw [stoppedVector_eq]
  exact stoppedNumerator_total R φ a z₀ ht J

 

theorem stoppedVector_bound {s : ℕ} (R φ : ℕ) (a : Fin s → ℕ) (z₀ : Fin s)
    (ht : (∑ z,a z)+φ=2^R) (J : ℕ) (z : Fin s) : stoppedVector R φ a z₀ J z≤2^(R*J) := by
  rw [← stoppedVector_total R φ a z₀ ht J]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)

end Contingency.IntegerTabulation

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

 

def graphArray (X : GraphState U r c) : Bool×Cell m n → Fin (U+1) :=
  fun w => ⟨(if w.1 then (graphUnderlying U r c X).x w.2 else (graphUnderlying U r c X).q w.2).toNat,by
    have h := (graph_feasible U r c X).1 w.2
    cases w.1 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩

theorem graphArray_injective : Function.Injective (graphArray U r c) := by
  intro X Y h
  apply graphUnderlying_injective U r c
  have hx : (graphUnderlying U r c X).x=(graphUnderlying U r c Y).x := by
    funext w
    have hh := congrArg Fin.val (congrFun h (true,w))
    dsimp [graphArray] at hh
    have hX := ((graph_feasible U r c X).1 w).1
    have hY := ((graph_feasible U r c Y).1 w).1
    omega
  have hq : (graphUnderlying U r c X).q=(graphUnderlying U r c Y).q := by
    funext w
    have hh := congrArg Fin.val (congrFun h (false,w))
    dsimp [graphArray] at hh
    have hX := ((graph_feasible U r c X).1 w).2.2.1
    have hY := ((graph_feasible U r c Y).1 w).2.2.1
    omega
  exact congrArg₂ State.mk hx hq

theorem graph_card_array : Nat.card (GraphState U r c)≤(U+1)^(2*(m*n)) := by
  rw [Nat.card_eq_fintype_card]
  simpa [Cell] using Fintype.card_le_of_injective (graphArray U r c) (graphArray_injective U r c)

theorem graph_card_dyadic (d b C : ℕ) (hmn : m*n≤d) (hU : U≤C) (hCb : C+1≤2^b) :
    Nat.card (GraphState U r c)≤2^(2*d*b) := by
  calc
    _ ≤ (U+1)^(2*(m*n)) := graph_card_array U r c
    _ ≤ (C+1)^(2*(m*n)) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (C+1)^(2*d) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (2^b)^(2*d) := Nat.pow_le_pow_left hCb _
    _ = _ := by rw [← pow_mul]; congr 1; ring

 

def completionArray (C : ℕ) (hC : ∀ i,paddedRow U L r c i≤C)
    (X : GraphState U r c) (A : Completion U L r c (graphUnderlying U r c X)) :
    Cell m n → Fin (C+1) := fun w => ⟨(A.val w).toNat,by
      have hlo := A.property.1 w
      have hhi := (completion_cell_le U L r c _ (graph_feasible U r c X) A w).trans (hC w.1)
      omega⟩

theorem completion_card_cap (C : ℕ) (hC : ∀ i,paddedRow U L r c i≤C) (X : GraphState U r c) :
    Nat.card (Completion U L r c (graphUnderlying U r c X))≤(C+1)^(m*n) := by
  let : Fintype (Completion U L r c (graphUnderlying U r c X)) := Fintype.ofFinite _
  have hinj : Function.Injective (completionArray U L r c C hC X) := by
    intro A B h
    apply Subtype.ext
    funext w
    have hh := congrArg Fin.val (congrFun h w)
    dsimp [completionArray] at hh
    have ha := A.property.1 w
    have hb := B.property.1 w
    omega
  rw [Nat.card_eq_fintype_card]
  simpa [Cell] using Fintype.card_le_of_injective _ hinj

theorem completion_card_dyadic (d b C : ℕ) (hmn : m*n≤d)
    (hC : ∀ i,paddedRow U L r c i≤C) (hCb : C+1≤2^b) (X : GraphState U r c) :
    Nat.card (Completion U L r c (graphUnderlying U r c X))≤2^(d*b) := by
  calc
    _ ≤ (C+1)^(m*n) := completion_card_cap U L r c C hC X
    _ ≤ (C+1)^d := Nat.pow_le_pow_right (by omega) hmn
    _ ≤ (2^b)^d := Nat.pow_le_pow_left hCb _
    _ = _ := by rw [← pow_mul]; congr 1; ring

end
end Contingency.PaddedGraph

 

 

 

namespace Contingency.BinaryArithmetic

open PosNum

 
def succCost : PosNum → ℕ
  | .one => 1
  | .bit0 _ => 1
  | .bit1 a => succCost a+1

theorem succCost_le (a : PosNum) : succCost a≤a.natSize := by
  induction a <;> simp_all [succCost,PosNum.natSize]

theorem succ_size_le (a : PosNum) : a.succ.natSize≤a.natSize+1 := by
  induction a <;> simp_all [PosNum.succ,PosNum.natSize]

 
theorem add_size_le (a b : PosNum) : (a+b).natSize≤a.natSize+b.natSize := by
  induction a generalizing b with
  | one =>
    change (PosNum.succ b).natSize≤1+b.natSize
    simpa [Nat.add_comm] using succ_size_le b
  | bit0 a ih =>
    cases b with
    | one => exact (succ_size_le a.bit0)
    | bit0 b => change (a+b).natSize+1≤(a.natSize+1)+(b.natSize+1); have := ih b; omega
    | bit1 b => change (a+b).natSize+1≤(a.natSize+1)+(b.natSize+1); have := ih b; omega
  | bit1 a ih =>
    cases b with
    | one => exact (succ_size_le a.bit1)
    | bit0 b => change (a+b).natSize+1≤(a.natSize+1)+(b.natSize+1); have := ih b; omega
    | bit1 b =>
      change (a+b).succ.natSize+1≤(a.natSize+1)+(b.natSize+1)
      have := succ_size_le (a+b)
      have := ih b
      omega

 

def addCost : PosNum → PosNum → ℕ
  | .one,b => succCost b+1
  | a,.one => succCost a+1
  | .bit0 a,.bit0 b => addCost a b+1
  | .bit1 a,.bit1 b => addCost a b+succCost (a+b)+2
  | .bit0 a,.bit1 b => addCost a b+1
  | .bit1 a,.bit0 b => addCost a b+1

theorem addCost_le (a b : PosNum) : addCost a b≤(a.natSize+b.natSize+1)^2 := by
  induction a generalizing b with
  | one =>
    have := succCost_le b
    simp only [addCost,PosNum.natSize]
    nlinarith
  | bit0 a ih =>
    cases b with
    | one => have := succCost_le a.bit0; simp only [addCost,PosNum.natSize,Nat.succ_eq_add_one] at *; nlinarith
    | bit0 b => have := ih b; simp only [addCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith [Nat.zero_le a.natSize,Nat.zero_le b.natSize]
    | bit1 b => have := ih b; simp only [addCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith [Nat.zero_le a.natSize,Nat.zero_le b.natSize]
  | bit1 a ih =>
    cases b with
    | one => have := succCost_le a.bit1; simp only [addCost,PosNum.natSize,Nat.succ_eq_add_one] at *; nlinarith
    | bit0 b => have := ih b; simp only [addCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith [Nat.zero_le a.natSize,Nat.zero_le b.natSize]
    | bit1 b =>
      have h := ih b
      have hs := (succCost_le (a+b)).trans (add_size_le a b)
      simp only [addCost,PosNum.natSize,Nat.succ_eq_add_one]
      nlinarith

 
def mulCost (a : PosNum) : PosNum → ℕ
  | .one => a.natSize+1
  | .bit0 b => mulCost a b+1
  | .bit1 b => mulCost a b+addCost ((a*b).bit0) a+2

theorem mul_size_le (a b : PosNum) : (a*b).natSize≤a.natSize+b.natSize := by
  have ha : (a:ℕ)<2^a.natSize := by rw [PosNum.natSize_to_nat]; exact Nat.size_le.mp le_rfl
  have hb : (b:ℕ)<2^b.natSize := by rw [PosNum.natSize_to_nat]; exact Nat.size_le.mp le_rfl
  rw [PosNum.natSize_to_nat,PosNum.mul_to_nat,Nat.size_le,pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le ha hb.le (by positivity)

theorem mulCost_le (a b : PosNum) :
    mulCost a b≤4*(a.natSize+b.natSize+1)^3 := by
  induction b with
  | one => simp only [mulCost,PosNum.natSize]; nlinarith [Nat.zero_le (a.natSize^3)]
  | bit0 b ih => simp only [mulCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith [Nat.zero_le a.natSize,Nat.zero_le b.natSize,Nat.zero_le (a.natSize*b.natSize)]
  | bit1 b ih =>
    have ha := addCost_le ((a*b).bit0) a
    have hs := mul_size_le a b
    simp only [PosNum.natSize] at ha
    have hh : ((a*b).natSize+1+a.natSize+1)^2≤(2*(a.natSize+b.natSize+1))^2 := by
      apply Nat.pow_le_pow_left
      omega
    have ha' := ha.trans hh
    simp only [mulCost,PosNum.natSize,Nat.succ_eq_add_one]
    nlinarith

 

theorem add_certificate (a b : PosNum) :
    ((a+b:PosNum):ℕ)=(a:ℕ)+(b:ℕ) ∧ addCost a b≤(a.natSize+b.natSize+1)^2 :=
  ⟨PosNum.add_to_nat a b,addCost_le a b⟩

theorem mul_certificate (a b : PosNum) :
    ((a*b:PosNum):ℕ)=(a:ℕ)*(b:ℕ) ∧ mulCost a b≤4*(a.natSize+b.natSize+1)^3 :=
  ⟨PosNum.mul_to_nat a b,mulCost_le a b⟩

end Contingency.BinaryArithmetic

 

 

open scoped BigOperators
namespace Contingency.BinaryArithmetic

 

def numAddCost : Num → Num → ℕ
  | .zero, b => b.natSize+1
  | a, .zero => a.natSize+1
  | .pos a, .pos b => addCost a b+1

def numMulCost : Num → Num → ℕ
  | .zero, _ => 1
  | _, .zero => 1
  | .pos a, .pos b => mulCost a b+1

theorem numAddCost_le (a b : Num) : numAddCost a b≤(a.natSize+b.natSize+2)^2 := by
  cases a with
  | zero => simp only [numAddCost,Num.natSize,zero_add]; nlinarith [Nat.zero_le b.natSize]
  | pos a =>
    cases b with
    | zero => simp only [numAddCost,Num.natSize,add_zero]; nlinarith [Nat.zero_le a.natSize]
    | pos b =>
      have h := addCost_le a b
      simp only [numAddCost,Num.natSize]
      nlinarith [Nat.zero_le a.natSize,Nat.zero_le b.natSize]

theorem numMulCost_le (a b : Num) : numMulCost a b≤5*(a.natSize+b.natSize+2)^3 := by
  cases a with
  | zero =>
    have h := Nat.one_le_pow 3 (b.natSize+2) (by omega)
    have hh : 1≤5*(b.natSize+2)^3 := by omega
    simpa only [numMulCost,Num.natSize,zero_add] using hh
  | pos a =>
    cases b with
    | zero =>
      change 1≤5*(a.natSize+2)^3
      have h := Nat.one_le_pow 3 (a.natSize+2) (by omega)
      omega
    | pos b =>
      have h := mulCost_le a b
      simp only [numMulCost,Num.natSize]
      nlinarith [Nat.zero_le ((a.natSize+b.natSize)^2),Nat.zero_le ((a.natSize+b.natSize)^3),Nat.zero_le a.natSize,Nat.zero_le b.natSize]

theorem numSize_le_of_lt (a : Num) (L : ℕ) (h : (a:ℕ)<2^L) : a.natSize≤L := by
  cases a with
  | zero => exact Nat.zero_le _
  | pos a =>
    change a.natSize≤L
    rw [PosNum.natSize_to_nat,Nat.size_le]
    exact h

 

def binaryDot : List (Num×Num) → Num×ℕ
  | [] => (.zero,1)
  | (a,b)::xs =>
    let t := binaryDot xs
    let p := a*b
    (p+t.1,t.2+numMulCost a b+numAddCost p t.1+3)

def dotValue (xs : List (Num×Num)) : ℕ := (xs.map (fun ab => (ab.1:ℕ)*(ab.2:ℕ))).sum

theorem binaryDot_value (xs : List (Num×Num)) : ((binaryDot xs).1:ℕ)=dotValue xs := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    simp only [binaryDot,Num.add_to_nat,Num.mul_to_nat,dotValue,List.map_cons,List.sum_cons] at *
    rw [ih]

 

theorem binaryDot_cost (xs : List (Num×Num)) (L : ℕ)
    (hx : ∀ ab∈xs,ab.1.natSize≤L ∧ ab.2.natSize≤L)
    (hv : dotValue xs<2^L) :
    (binaryDot xs).2≤1+xs.length*(10*(2*L+2)^3) := by
  induction xs with
  | nil => simp [binaryDot]
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    have hv' : (a:ℕ)*(b:ℕ)+dotValue xs<2^L := hv
    have hp : (a:ℕ)*(b:ℕ)<2^L := (Nat.le_add_right _ _).trans_lt hv'
    have ht : dotValue xs<2^L := (Nat.le_add_left _ _).trans_lt hv'
    have hab := hx (a,b) (by simp)
    dsimp only at hab
    have hc := ih (fun ab h => hx ab (by simp [h])) ht
    have hs := numSize_le_of_lt (a*b) L (by simpa only [Num.mul_to_nat] using hp)
    have hst := numSize_le_of_lt (binaryDot xs).1 L (by simpa only [binaryDot_value] using ht)
    have hm := (numMulCost_le a b).trans (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (by omega : a.natSize+b.natSize+2≤2*L+2) 3))
    have ha := (numAddCost_le (a*b) (binaryDot xs).1).trans
      (Nat.pow_le_pow_left (by omega : (a*b).natSize+(binaryDot xs).1.natSize+2≤2*L+2) 2)
    have he : (2*L+2)^2≤(2*L+2)^3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hu : 1≤(2*L+2)^3 := Nat.one_le_pow _ _ (by omega)
    simp only [binaryDot,List.length_cons]
    nlinarith only [hc,hm,ha,he,hu]

 
def binaryColumn {s : ℕ} (A : Fin s → Fin s → Num) (v : Fin s → Num) (j : Fin s) : Num×ℕ :=
  binaryDot (List.ofFn (fun i => (v i,A i j)))

theorem binaryColumn_value {s : ℕ} (A : Fin s → Fin s → Num) (v : Fin s → Num) (j : Fin s) :
    ((binaryColumn A v j).1:ℕ)=IntegerTabulation.step (fun i j => (A i j:ℕ)) (fun i => (v i:ℕ)) j := by
  rw [binaryColumn,binaryDot_value]
  simp [dotValue,IntegerTabulation.step,List.map_ofFn,List.sum_ofFn]

 
def binaryPropagate {s : ℕ} (A : Fin s → Fin s → Num) (v : Fin s → Num) : ℕ → (Fin s → Num)
  | 0 => v
  | t+1 =>
    let previous := binaryPropagate A v t
    fun j => (binaryColumn A previous j).1

theorem binaryPropagate_value {s : ℕ} (A : Fin s → Fin s → Num) (v : Fin s → Num) (t : ℕ) :
    (fun i => (binaryPropagate A v t i:ℕ))=
      IntegerTabulation.propagate (fun i j => (A i j:ℕ)) (fun i => (v i:ℕ)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    simp only [binaryPropagate,binaryColumn_value,IntegerTabulation.propagate,ih]

end Contingency.BinaryArithmetic

 

 

open scoped BigOperators
namespace Contingency.BinaryArithmetic

variable {s : ℕ} (A : Fin s → Fin s → Num) (v : Fin s → Num) (Q R : ℕ)
    (hA : ∀ i,∑ j,(A i j:ℕ)=2^Q) (hv : ∑ i,(v i:ℕ)=2^R)

 
theorem denominator_size (x B : ℕ) (hx : x≤2^B) : x<2^(B+1) := by
  exact hx.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B))

include hA hv in
theorem binaryColumn_cost (t : ℕ) (j : Fin s) :
    (binaryColumn A (binaryPropagate A v t) j).2≤
      1+s*(10*(2*(R+(t+1)*Q+1)+2)^3) := by
  let L := R+(t+1)*Q+1
  have hval := binaryPropagate_value A v t
  have hvec (i : Fin s) : (binaryPropagate A v t i:ℕ)≤2^(R+t*Q) := by
    rw [show (binaryPropagate A v t i:ℕ)=
      IntegerTabulation.propagate (fun i j => (A i j:ℕ)) (fun i => (v i:ℕ)) t i from congrFun hval i]
    exact IntegerTabulation.propagate_entry_bound _ _ Q R hA hv t i
  have hentry (i l : Fin s) : (A i l:ℕ)≤2^Q := by
    rw [← hA i]
    exact Finset.single_le_sum (fun l _ => Nat.zero_le (A i l:ℕ)) (Finset.mem_univ l)
  have hi : Q≤R+(t+1)*Q := by nlinarith only [Nat.zero_le R,Nat.zero_le (t*Q)]
  unfold binaryColumn
  have hh := binaryDot_cost (List.ofFn (fun i => (binaryPropagate A v t i,A i j))) L
  rw [List.length_ofFn] at hh
  apply hh
  · intro ab hab
    rcases List.mem_ofFn.mp hab with ⟨i,rfl⟩
    constructor
    · apply numSize_le_of_lt
      change (binaryPropagate A v t i:ℕ)<2^(R+(t+1)*Q+1)
      apply denominator_size
      exact (hvec i).trans (Nat.pow_le_pow_right (by norm_num) (by gcongr; omega))
    · apply numSize_le_of_lt
      change (A i j:ℕ)<2^(R+(t+1)*Q+1)
      exact denominator_size _ _ ((hentry i j).trans (Nat.pow_le_pow_right (by norm_num) hi))
  · change _<2^(R+(t+1)*Q+1)
    apply denominator_size
    rw [← binaryDot_value]
    change ((binaryColumn A (binaryPropagate A v t) j).1:ℕ)≤_
    rw [binaryColumn_value,hval]
    exact IntegerTabulation.propagate_entry_bound _ _ Q R hA hv (t+1) j

 

def binaryPropagationCost : ℕ → ℕ
  | 0 => 0
  | t+1 => binaryPropagationCost t+∑ j,(binaryColumn A (binaryPropagate A v t) j).2

include hA hv in
theorem binaryPropagationCost_le_aux (T : ℕ) (t : ℕ) (ht : t≤T) :
    binaryPropagationCost A v t≤t*s*(1+s*(10*(2*(R+T*Q+1)+2)^3)) := by
  induction t with
  | zero => simp [binaryPropagationCost]
  | succ t ih =>
    have hi := ih (by omega)
    have hcol (j : Fin s) := binaryColumn_cost A v Q R hA hv t j
    have hb : R+(t+1)*Q+1≤R+T*Q+1 := by gcongr
    have hm : (∑ j,(binaryColumn A (binaryPropagate A v t) j).2)≤
        s*(1+s*(10*(2*(R+T*Q+1)+2)^3)) := by
      calc
        _ ≤ ∑ _ : Fin s,(1+s*(10*(2*(R+T*Q+1)+2)^3)) := by
          apply Finset.sum_le_sum
          intro j _
          exact (hcol j).trans (by gcongr)
        _ = _ := by simp
    rw [binaryPropagationCost]
    nlinarith only [hi,hm]

include hA hv in
theorem binaryPropagationCost_le (T : ℕ) :
    binaryPropagationCost A v T≤T*s*(1+s*(10*(2*(R+T*Q+1)+2)^3)) :=
  binaryPropagationCost_le_aux A v Q R hA hv T T le_rfl

end Contingency.BinaryArithmetic

end

end OAI
