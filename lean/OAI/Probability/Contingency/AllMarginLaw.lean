import Mathlib
import OAI.Probability.Contingency.DirectCases
import OAI.Probability.Contingency.ParseNatRuns

namespace OAI

/-! All Margin Law. -/

noncomputable section

open scoped BigOperators
open Filter
open scoped BigOperators
namespace Contingency
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local instance allMarginLawTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

namespace Parameters

 
theorem D_positive (m n N : ℕ) : 0<D m n N := by
  have hd : 0<dim m n := by unfold dim; omega
  have hb : 0<bits m n N := lt_of_lt_of_le hd (dimension_le_bits _ _ _)
  exact Nat.mul_pos (Nat.pow_pos hd) (Nat.pow_pos hb)

 
theorem table_card_D_all (hrc : (∑ i,r i)=∑ j,c j) :
    Nat.card (Tables r c)≤2^D m n (∑ i,r i) := by
  by_cases hm : m=0
  · let := tables_nonempty r c hrc
    let := table_subsingleton_of_direct r c (Or.inl hm)
    rw [Nat.card_unique]
    exact Nat.one_le_pow _ _ (by norm_num)
  by_cases hn : n=0
  · let := tables_nonempty r c hrc
    let := table_subsingleton_of_direct r c (Or.inr (Or.inl hn))
    rw [Nat.card_unique]
    exact Nat.one_le_pow _ _ (by norm_num)
  exact table_card_D r c (by omega) (by omega)

 
theorem bits_le_input (m n N : ℕ) : bits m n N≤26*(inputSize m n N+3)^2 := by
  have hd := dim_le_size_square m n N
  have hb := bits_le m n N
  have hs : 1≤ inputSize m n N+3 := by omega
  have hl : Nat.log2 (N+1)≤ inputSize m n N+3 := by unfold inputSize; omega
  have hs2 : inputSize m n N+3≤(inputSize m n N+3)^2 := by nlinarith
  nlinarith

theorem D_le_input (m n N : ℕ) : D m n N≤26^2*(inputSize m n N+3)^16 := by
  have hd := dim_le_size_square m n N
  have hb := bits_le_input m n N
  unfold D
  calc
    _ ≤ ((inputSize m n N+3)^2)^6*(26*(inputSize m n N+3)^2)^2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left hb _)
    _ = _ := by ring

 
theorem schedule_base_le_input (m n N k : ℕ) :
    dim m n+bits m n N+k+2≤32*(inputSize m n N+k+3)^2 := by
  have hd := dim_le_size_square m n N
  have hb := bits_le_input m n N
  have hs : inputSize m n N+3≤ inputSize m n N+k+3 := by omega
  have hs2 := Nat.pow_le_pow_left hs 2
  have hx : 1≤ inputSize m n N+k+3 := by omega
  have hx2 : inputSize m n N+k+3≤(inputSize m n N+k+3)^2 := by
    nlinarith only [hx]
  omega

end Parameters

 

theorem arbitraryDraw_bits_input (hrc : (∑ i,r i)=∑ j,c j) (k : ℕ) (hk : 1≤k) :
    (arbitraryDraw r c hrc k).bits≤
      (32*(inputSize m n (∑ i,r i)+k+3)^2)^300 := by
  classical
  unfold arbitraryDraw
  split_ifs with h
  · exact Nat.zero_le _
  · rw [PaddedGraph.canonicalDraw_bits]
    have hm : 0 < m := by by_contra hh; exact h (Or.inl (by omega))
    have hn : 0 < n := by by_contra hh; exact h (Or.inr (Or.inl (by omega)))
    have hd := Parameters.dimensions hm hn
    have hb := Parameters.dimension_le_bits m n (∑ i,r i)
    have hR := (Schedule.bounds _ _ k hd.1 hb hk).2.2.2.2.2.2.2.2.2
    exact hR.trans (pow_le_pow_left₀ (Nat.zero_le _)
      (Parameters.schedule_base_le_input m n (∑ i,r i) k) 300)

local notation "D" => Parameters.D m n (∑ i,r i)
variable (hrc : (∑ i,r i)=∑ j,c j)
local notation "p" => arbitraryDraw r c hrc (2*D)

 
def arbitraryResidual (X : Tables r c) : ℕ := correctionCount p D X

theorem arbitraryResidual_data :
    (∀ X : Tables r c, (arbitraryResidual r c hrc X:ℤ)=
      (2:ℤ)^((p).bits+D)-(Fintype.card (Tables r c):ℤ)*((2:ℤ)^D-1)*(p).count X) ∧
    (∑ X,arbitraryResidual r c hrc X)=Fintype.card (Tables r c)*2^(p).bits := by
  let := tables_nonempty r c hrc
  exact correction_counts p D
    (by simpa only [Nat.card_eq_fintype_card] using Parameters.table_card_D_all r c hrc)
    (arbitraryDraw_tv r c hrc _ (by have := Parameters.D_positive m n (∑ i,r i); omega))

theorem arbitraryResidual_total_pos : 0<∑ X,arbitraryResidual r c hrc X := by
  let := tables_nonempty r c hrc
  rw [(arbitraryResidual_data r c hrc).2]
  exact Nat.mul_pos Fintype.card_pos (by positivity)

 

theorem arbitrary_corrected_exact (X : Tables r c) :
    letI := Classical.decEq (Tables r c)
    (1-1/(2:ℝ)^D)*(p).toLaw.mass X+(1/(2:ℝ)^D)*
      (∑' j : ℕ,IntegerDraw.stoppingMass (arbitraryResidual r c hrc) j X)=
        1/(Fintype.card (Tables r c):ℝ) := by
  classical
  let := tables_nonempty r c hrc
  have hM : Fintype.card (Tables r c)≤2^D := by
    simpa only [Nat.card_eq_fintype_card] using Parameters.table_card_D_all r c hrc
  have ht := arbitraryDraw_tv r c hrc (2*D)
    (by have := Parameters.D_positive m n (∑ i,r i); omega)
  rw [IntegerDraw.rejection_exact _ (arbitraryResidual_total_pos r c hrc) X,
    (arbitraryResidual_data r c hrc).2]
  push_cast
  exact corrected_exact p D hM ht X

end
end Contingency

 

 

namespace Contingency.BinaryArithmetic

 
def predCost : PosNum → ℕ
  | .one => 1
  | .bit1 _ => 1
  | .bit0 a => predCost a+2

theorem predCost_le (a : PosNum) : predCost a ≤ 2*a.natSize := by
  induction a <;> simp_all [predCost,PosNum.natSize,Nat.succ_eq_add_one] <;> omega

theorem pred_size_le (a : PosNum) : a.pred'.natSize ≤ a.natSize := by
  rw [Num.natSize_to_nat,PosNum.pred'_to_nat,PosNum.natSize_to_nat]
  exact Nat.size_le_size (Nat.pred_le _)

 
def signedSize (z : ZNum) : ℕ := z.abs.natSize

@[simp] theorem signedSize_pos (a : PosNum) : signedSize (.pos a)=a.natSize := rfl
@[simp] theorem signedSize_neg (a : PosNum) : signedSize (.neg a)=a.natSize := rfl
@[simp] theorem signedSize_zero : signedSize 0=0 := rfl
@[simp] theorem signedSize_toZNum (a : Num) : signedSize a.toZNum=a.natSize := by cases a <;> rfl
@[simp] theorem signedSize_toZNumNeg (a : Num) : signedSize a.toZNumNeg=a.natSize := by cases a <;> rfl

theorem signedSize_bit0 (a : ZNum) : signedSize a.bit0 ≤ signedSize a+1 := by
  cases a <;> simp [signedSize,ZNum.bit0,ZNum.abs,Num.natSize,PosNum.natSize,Nat.succ_eq_add_one]

theorem predCase_size (a : Num) : (Num.casesOn (motive := fun _ => PosNum) a 1 PosNum.bit1).natSize ≤ a.natSize+1 := by
  cases a <;> simp [Num.natSize,PosNum.natSize,Nat.succ_eq_add_one]

theorem signedSize_bit1 (a : ZNum) : signedSize a.bit1 ≤ signedSize a+1 := by
  cases a with
  | zero => decide
  | pos a => exact le_rfl
  | neg a =>
    change (Num.casesOn (motive := fun _ => PosNum) a.pred' 1 PosNum.bit1).natSize ≤ a.natSize+1
    exact (predCase_size a.pred').trans (by have := pred_size_le a; omega)

theorem signedSize_bitm1 (a : ZNum) : signedSize a.bitm1 ≤ signedSize a+1 := by
  cases a with
  | zero => decide
  | neg a => exact le_rfl
  | pos a =>
    change (Num.casesOn (motive := fun _ => PosNum) a.pred' 1 PosNum.bit1).natSize ≤ a.natSize+1
    exact (predCase_size a.pred').trans (by have := pred_size_le a; omega)

theorem sub'_size (a b : PosNum) : signedSize (a.sub' b) ≤ a.natSize+b.natSize := by
  induction a generalizing b with
  | one =>
    change signedSize ((1:PosNum).sub' b) ≤ _
    rw [PosNum.one_sub',signedSize_toZNumNeg]
    have := pred_size_le b
    simp only [PosNum.natSize]; omega
  | bit0 a ih =>
    cases b with
    | one =>
      change signedSize ((PosNum.bit0 a).pred'.toZNum) ≤ _
      rw [signedSize_toZNum]
      exact (pred_size_le a.bit0).trans (by omega)
    | bit0 b =>
      have := (signedSize_bit0 (a.sub' b)).trans (Nat.add_le_add_right (ih b) 1)
      simp only [PosNum.sub',PosNum.natSize,Nat.succ_eq_add_one]; omega
    | bit1 b =>
      have := (signedSize_bitm1 (a.sub' b)).trans (Nat.add_le_add_right (ih b) 1)
      simp only [PosNum.sub',PosNum.natSize,Nat.succ_eq_add_one]; omega
  | bit1 a ih =>
    cases b with
    | one =>
      change signedSize ((PosNum.bit1 a).pred'.toZNum) ≤ _
      rw [signedSize_toZNum]
      exact (pred_size_le a.bit1).trans (by omega)
    | bit0 b =>
      have := (signedSize_bit1 (a.sub' b)).trans (Nat.add_le_add_right (ih b) 1)
      simp only [PosNum.sub',PosNum.natSize,Nat.succ_eq_add_one]; omega
    | bit1 b =>
      have := (signedSize_bit0 (a.sub' b)).trans (Nat.add_le_add_right (ih b) 1)
      simp only [PosNum.sub',PosNum.natSize,Nat.succ_eq_add_one]; omega

 
def signedBitCost : ZNum → ℕ
  | .zero => 2
  | .pos a => predCost a+2
  | .neg a => predCost a+2

theorem signedBitCost_le (a : ZNum) : signedBitCost a ≤ 2*signedSize a+2 := by
  cases a with
  | zero => decide
  | pos a => have := predCost_le a; simpa only [signedBitCost,signedSize_pos] using Nat.add_le_add_right this 2
  | neg a => have := predCost_le a; simpa only [signedBitCost,signedSize_neg] using Nat.add_le_add_right this 2

 
def subCost : PosNum → PosNum → ℕ
  | a,.one => predCost a+2
  | .one,b => predCost b+2
  | .bit0 a,.bit0 b => subCost a b+2
  | .bit1 a,.bit1 b => subCost a b+2
  | .bit0 a,.bit1 b => subCost a b+signedBitCost (a.sub' b)+2
  | .bit1 a,.bit0 b => subCost a b+signedBitCost (a.sub' b)+2

theorem subCost_le (a b : PosNum) : subCost a b ≤ 4*(a.natSize+b.natSize+1)^2 := by
  induction a generalizing b with
  | one =>
    cases b with
    | one => decide
    | bit0 b =>
      have := predCost_le b.bit0
      simp only [subCost,PosNum.natSize,Nat.succ_eq_add_one] at *
      nlinarith [Nat.zero_le b.natSize]
    | bit1 b =>
      have := predCost_le b.bit1
      simp only [subCost,PosNum.natSize,Nat.succ_eq_add_one] at *
      nlinarith [Nat.zero_le b.natSize]
  | bit0 a ih =>
    cases b with
    | one => have := predCost_le a.bit0; simp only [subCost,PosNum.natSize,Nat.succ_eq_add_one] at *; nlinarith
    | bit0 b => have := ih b; simp only [subCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith [Nat.zero_le a.natSize,Nat.zero_le b.natSize]
    | bit1 b =>
      have := ih b
      have hk : signedBitCost (a.sub' b) ≤ 2*(a.natSize+b.natSize)+2 :=
        (signedBitCost_le (a.sub' b)).trans (by have := sub'_size a b; omega)
      simp only [subCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith
  | bit1 a ih =>
    cases b with
    | one => have := predCost_le a.bit1; simp only [subCost,PosNum.natSize,Nat.succ_eq_add_one] at *; nlinarith
    | bit0 b =>
      have := ih b
      have hk : signedBitCost (a.sub' b) ≤ 2*(a.natSize+b.natSize)+2 :=
        (signedBitCost_le (a.sub' b)).trans (by have := sub'_size a b; omega)
      simp only [subCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith
    | bit1 b => have := ih b; simp only [subCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith [Nat.zero_le a.natSize,Nat.zero_le b.natSize]

 
def divisionAuxCost (r : Num) (d : PosNum) : ℕ :=
  match r with
  | .zero => d.natSize+4
  | .pos a => subCost a d+4

theorem divisionAuxCost_le (r : Num) (d : PosNum) :
    divisionAuxCost r d ≤ 5*(r.natSize+d.natSize+2)^2 := by
  cases r with
  | zero => simp only [divisionAuxCost,Num.natSize]; nlinarith [Nat.zero_le d.natSize]
  | pos a =>
    have := subCost_le a d
    simp only [divisionAuxCost,Num.natSize]; nlinarith [Nat.zero_le a.natSize,Nat.zero_le d.natSize]

 

def divisionCost (d : PosNum) : PosNum → ℕ
  | .one => divisionAuxCost 1 d+2
  | .bit0 n => divisionCost d n+divisionAuxCost (Num.bit0 (d.divMod n).2) d+2
  | .bit1 n => divisionCost d n+divisionAuxCost (Num.bit1 (d.divMod n).2) d+2

theorem remainder_size (d n : PosNum) : (d.divMod n).2.natSize ≤ d.natSize := by
  apply numSize_le_of_lt
  rw [← (PosNum.divMod_to_nat d n).2]
  have hd : (d:ℕ)<2^d.natSize := by rw [PosNum.natSize_to_nat]; exact Nat.size_le.mp le_rfl
  exact (Nat.mod_lt _ (PosNum.to_nat_pos d)).trans hd

theorem numBit0_size (n : Num) : (Num.bit0 n).natSize ≤ n.natSize+1 := by
  cases n <;> simp [Num.bit0,Num.natSize,PosNum.natSize,Nat.succ_eq_add_one]

theorem numBit1_size (n : Num) : (Num.bit1 n).natSize ≤ n.natSize+1 := by
  cases n <;> simp [Num.bit1,Num.natSize,PosNum.natSize,Nat.succ_eq_add_one]

theorem divisionCost_le (d n : PosNum) :
    divisionCost d n ≤ n.natSize*(7*(2*d.natSize+3)^2) := by
  have haux (r : Num) (hr : r.natSize ≤ d.natSize+1) :
      divisionAuxCost r d+2 ≤ 7*(2*d.natSize+3)^2 := by
    have hh := (divisionAuxCost_le r d).trans
      (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (by omega : r.natSize+d.natSize+2 ≤ 2*d.natSize+3) 2))
    nlinarith [Nat.zero_le d.natSize]
  induction n with
  | one =>
    simpa only [divisionCost,PosNum.natSize,one_mul] using haux 1 (by change 1 ≤ d.natSize+1; omega)
  | bit0 n ih =>
    have hh := haux (Num.bit0 (d.divMod n).2)
      ((numBit0_size _).trans (Nat.add_le_add_right (remainder_size d n) 1))
    simp only [divisionCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith only [ih,hh]
  | bit1 n ih =>
    have hh := haux (Num.bit1 (d.divMod n).2)
      ((numBit1_size _).trans (Nat.add_le_add_right (remainder_size d n) 1))
    simp only [divisionCost,PosNum.natSize,Nat.succ_eq_add_one]; nlinarith only [ih,hh]

 

theorem division_certificate (d n : PosNum) :
    ((d.divMod n).1:ℕ)=(n:ℕ)/(d:ℕ) ∧
    ((d.divMod n).2:ℕ)=(n:ℕ)%(d:ℕ) ∧
    divisionCost d n ≤ n.natSize*(7*(2*d.natSize+3)^2) :=
  ⟨(PosNum.divMod_to_nat d n).1.symm,(PosNum.divMod_to_nat d n).2.symm,divisionCost_le d n⟩

end Contingency.BinaryArithmetic

 

 

open scoped BigOperators
namespace Contingency
noncomputable section

namespace Grid

theorem vertex_card (q K : ℕ) : Nat.card (Vertex q K)=K^q := by
  rw [Nat.card_eq_fintype_card]
  simp [Vertex]

theorem vertex_card_dyadic {q K d b : ℕ} (hq : q≤d) (hK : K≤2^b) :
    Nat.card (Vertex q K)≤2^(d*b) := by
  rw [vertex_card]
  calc
    K^q ≤ (2^b)^q := Nat.pow_le_pow_left hK _
    _ ≤ (2^b)^d := Nat.pow_le_pow_right (by positivity) hq
    _ = _ := by rw [← pow_mul]; congr 1; ring

end Grid
namespace Dense

theorem offsets_card_dyadic {q d b : ℕ} (w : Fin q → ℕ)
    (hq : q≤d) (hw : ∀ i,w i≤2^b) : Nat.card (Offsets w)≤2^(d*b) := by
  rw [Nat.card_eq_fintype_card]
  simp only [Offsets,Fintype.card_pi,Fintype.card_fin]
  calc
    (∏ i,w i) ≤ ∏ i : Fin q,2^b := Finset.prod_le_prod (fun i _ => hw i)
    _ = (2^b)^q := by simp
    _ ≤ (2^b)^d := Nat.pow_le_pow_right (by positivity) hq
    _ = _ := by rw [← pow_mul]; congr 1; ring

end Dense
namespace IntegerTabulation

 

def arithmeticTerms (S V H JD T Jo : ℕ) : ℕ :=
  S*(H*V^2+V^3+JD*V)+S^2*V+T*S^2+S*V^2+Jo*V

 

theorem arithmeticTerms_bound (e H JD T Jo : ℕ) :
    arithmeticTerms (2^(2*e)) (2^e) H JD T Jo≤
      2^(10*e)*(H+JD+T+Jo+3) := by
  let V := 2^e
  have hV : 1≤V := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 2^(2*e)=V^2 := by dsimp [V]; rw [← pow_mul]; congr 1; omega
  have h10 : 2^(10*e)=V^10 := by dsimp [V]; rw [← pow_mul]; congr 1; omega
  rw [h2,h10]
  change arithmeticTerms (V^2) V H JD T Jo≤_
  have hp (a : ℕ) (ha : a≤10) : V^a≤V^10 := Nat.pow_le_pow_right hV ha
  unfold arithmeticTerms
  calc
    _ = H*V^4+V^5+JD*V^3+V^5+T*V^4+V^4+Jo*V := by ring
    _ ≤ H*V^10+V^10+JD*V^10+V^10+T*V^10+V^10+Jo*V^10 := by
      gcongr <;> first | omega | simpa using hp 1 (by omega)
    _ = _ := by ring

end IntegerTabulation
end
end Contingency

 

 

open scoped BigOperators
namespace Contingency.Dense.BinProblem
open Contingency.Grid
variable {a c q K : ℕ}

 
def cornerEntries (D : BinProblem a c q K) (v : Vertex q K) :
    Fin (a+1) → Fin (c+1) → ℤ :=
  integerComplete D.R D.P (fun i j => D.w (D.e.symm (i,j))*(v (D.e.symm (i,j))).val)

 

def rationalPenalty (D : BinProblem a c q K) (d : ℕ) (v : Vertex q K) : ℚ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty fun s : Fin (a+1)×Fin (c+1) =>
    -(D.cornerEntries v s.1 s.2:ℚ)/(min (D.R s.1) (D.P s.2):ℕ)-(d:ℚ)/(d:ℚ)^8)

 
def rationalExponent (D : BinProblem a c q K) (d : ℕ) (v : Vertex q K) : ℕ :=
  (⌊(d:ℚ)^4*D.rationalPenalty d v⌋:ℤ).toNat

noncomputable section
variable (D : BinProblem a c q K)

theorem cornerEntries_cast (v : Vertex q K) (i j) :
    (D.cornerEntries v i j:ℝ)=
      scaled (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths
        (fun s => realCorner v (D.e.symm s)) i j := by
  unfold cornerEntries
  rw [integerComplete_cast]
  congr 1
  funext i j
  simp [widths,realCorner]

theorem rationalPenalty_cast (d : ℕ) (hD : D.d=d) (v : Vertex q K) :
    (D.rationalPenalty d v:ℝ)=
      penalty (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths
        (D.d^8) D.d (fun s => realCorner v (D.e.symm s)) := by
  unfold rationalPenalty penalty
  rw [Rat.cast_max]
  simp only [Rat.cast_zero]
  congr 1
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x : ℚ => (x:ℝ))
    (fun x y => Rat.cast_max x y)]
  congr 1
  funext s
  simp only [Function.comp_apply,Rat.cast_sub,Rat.cast_div,Rat.cast_neg,
    Rat.cast_intCast,Rat.cast_natCast,Rat.cast_pow,Nat.cast_min]
  rw [D.cornerEntries_cast]
  simp [normalized,scale,hD,Rat.cast_min,neg_div]

theorem rationalExponent_eq (d : ℕ) (hD : D.d=d) (v : Vertex q K) :
    D.rationalExponent d v=D.exponent v := by
  unfold rationalExponent exponent
  congr 1
  rw [← Rat.floor_cast (α:=ℝ)]
  simp only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,D.rationalPenalty_cast d hD]
  unfold binExponent
  rw [hD]

end
end Contingency.Dense.BinProblem

 

 

open scoped BigOperators
namespace Contingency.Dense.BinProblem
open Contingency.Grid
variable {a c q K : ℕ}

 

def cellExponent (D : BinProblem a c q K) (d : ℕ) (v : Vertex q K)
    (i : Fin (a+1)) (j : Fin (c+1)) : ℤ :=
  ((-D.cornerEntries v i j*(d:ℤ)^8-(d:ℤ)*(min (D.R i) (D.P j):ℕ))*(d:ℤ)^4) /
    ((min (D.R i) (D.P j)*d^8:ℕ):ℤ)

def integerExponent (D : BinProblem a c q K) (d : ℕ) (v : Vertex q K) : ℕ :=
  (max 0 (Finset.univ.sup' Finset.univ_nonempty
    (fun s : Fin (a+1)×Fin (c+1) => D.cellExponent d v s.1 s.2))).toNat

noncomputable section
variable (D : BinProblem a c q K)

theorem cellExponent_eq (d : ℕ) (hd : 0<d) (v : Vertex q K) (i j) :
    D.cellExponent d v i j=
      ⌊(d:ℚ)^4*(-(D.cornerEntries v i j:ℚ)/(min (D.R i) (D.P j):ℕ)-(d:ℚ)/(d:ℚ)^8)⌋ := by
  have hs : (0:ℚ)<(min (D.R i) (D.P j):ℕ) := by
    exact_mod_cast lt_min (D.hR i) (D.hP j)
  have hdp : (0:ℚ)<d := by exact_mod_cast hd
  unfold cellExponent
  rw [← Rat.floor_intCast_div_natCast]
  simp only [Int.cast_mul,Int.cast_sub,Int.cast_neg,Int.cast_natCast,Int.cast_pow,Nat.cast_mul,Nat.cast_pow]
  congr 1
  field_simp [hs.ne',hdp.ne']

 

theorem integerExponent_eq_rational (d : ℕ) (hd : 0<d) (v : Vertex q K) :
    D.integerExponent d v=D.rationalExponent d v := by
  unfold integerExponent rationalExponent rationalPenalty
  congr 1
  rw [mul_max_of_nonneg _ _ (by positivity),mul_zero,Int.floor_mono.map_max,Int.floor_zero]
  congr 1
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x : ℚ => (d:ℚ)^4*x)
    (fun x y => mul_max_of_nonneg x y (by positivity))]
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x : ℚ => (⌊x⌋:ℤ))
    (fun x y => Int.floor_mono.map_max)]
  congr 1
  funext s
  exact D.cellExponent_eq d hd v s.1 s.2

theorem integerExponent_eq (d : ℕ) (hD : D.d=d) (v : Vertex q K) :
    D.integerExponent d v=D.exponent v := by
  have hd : 0<d := by have := D.hd; rw [hD] at this; exact_mod_cast (show (0:ℝ)<d by linarith)
  rw [D.integerExponent_eq_rational d hd v,D.rationalExponent_eq d hD v]

end
end Contingency.Dense.BinProblem

 

 

 

namespace Contingency.BitModel.StackCode.HighPad

def pushCode : Fin 2→Op 2 8
  | 0 => .push 6 false 1
  | _ => .halt
abbrev pushProgram : Program := ⟨2,8,0,pushCode⟩
abbrev back : Program := Sequence.program pushProgram 4 0 (Transfer.code (6 : Fin 8) 5)
abbrev program : Program := Sequence.program (Transfer.program (5 : Fin 8) 6) back.labels back.start back.code

theorem push_noCoin (q) : NoCoin (pushProgram.code q) := by fin_cases q <;> trivial
theorem back_noCoin : ∀ q,NoCoin (back.code q) := by
  apply noCoin_sequence _ _ _ _ push_noCoin
  intro q; fin_cases q <;> trivial
theorem noCoin : ∀ q,NoCoin (program.code q) := by
  apply noCoin_sequence (Transfer.program (5 : Fin 8) 6) back.labels back.start back.code ?_ back_noCoin
  intro q; fin_cases q <;> trivial

theorem back_run (bs : List Bool) (m : Memory 8) (h : m.stack 6=bs) :
    (List.replicate (2+(2*(bs.length+1)+2)) false).foldl (fun c b => step back b c)
      ⟨some back.start,m⟩=
      ⟨none,Transfer.memory (6 : Fin 8) (5 : Fin 8) (false::bs) (m.push 6 false)⟩ := by
  have hf : Sequence.FirstHalt pushProgram ⟨some pushProgram.start,m⟩ [false,false] :=
by
    constructor
    · intro h; cases h
    constructor
    · intro h; cases h
    rfl
  have he := Sequence.link_run pushProgram 4 0 (Transfer.code (6 : Fin 8) 5)
    ⟨some pushProgram.start,m⟩ [false,false] (List.replicate (2*(bs.length+1)+2) false) hf
  have ht := Transfer.run (6 : Fin 8) 5 (by decide) (false::bs) (m.push 6 false)
    (by simp [Memory.push,h])
  change (List.replicate (2*(bs.length+1)+2) false).foldl
    (fun c b => step (Transfer.program (6 : Fin 8) 5) b c)
    ⟨some (0 : Fin 4),m.push 6 false⟩=_ at ht
  rw [List.replicate_add]
  change ([false,false]++List.replicate (2*(bs.length+1)+2) false).foldl
    (fun c b => step back b c) ⟨some back.start,m⟩=_
  change ([false,false]++List.replicate (2*(bs.length+1)+2) false).foldl
    (fun c b => step back b c) ⟨some back.start,m⟩=
      Sequence.right pushProgram 4 0 (Transfer.code (6 : Fin 8) 5)
        ((List.replicate (2*(bs.length+1)+2) false).foldl
          (fun c b => step (Transfer.program (6 : Fin 8) 5) b c) ⟨some (0 : Fin 4),m.push 6 false⟩) at he
  exact he.trans (congrArg (Sequence.right pushProgram 4 0 (Transfer.code (6 : Fin 8) 5)) ht)

 

theorem pad (bs : List Bool) (m : Memory 8) (h5 : m.stack 5=bs) (h6 : m.stack 6=[]) :
    ∃ (t : ℕ) (m' : Memory 8),t≤4*bs.length+8 ∧ m'.stack 5=bs++[false] ∧
      m'.stack 6=[] ∧ (∀ i : Fin 8,i≠5 → i≠6 → m'.stack i=m.stack i) ∧
      m'.input=m.input ∧ m'.outputRev=m.outputRev ∧
      ∀ coins : List Bool,coins.length=t →
        coins.foldl (fun c b => step program b c) ⟨some program.start,m⟩=⟨none,m'⟩ := by
  let m₁ := Transfer.memory (5 : Fin 8) 6 bs m
  have hrun := Transfer.run (5 : Fin 8) 6 (by decide) bs m h5
  have hm₁ := Transfer.memory_fields (5 : Fin 8) 6 (by decide) bs m h5
  have hs6 : m₁.stack 6=bs.reverse := by simpa [m₁,h6] using hm₁.2.1
  let m₂ := Transfer.memory (6 : Fin 8) (5 : Fin 8) (false::bs.reverse) (m₁.push 6 false)
  have hs : (m₁.push 6 false).stack 6=false::bs.reverse := by simp [Memory.push,hs6]
  have hm₂ := Transfer.memory_fields (6 : Fin 8) 5 (by decide) (false::bs.reverse) (m₁.push 6 false) hs
  have hhal : (Transfer.exec (5 : Fin 8) 6 (2*bs.length+2) (Transfer.config 5 6 0 m)).state=none := by rw [hrun]
  obtain ⟨k,hk,hfirst⟩ := Sequence.deterministic_first_time (Transfer.program (5 : Fin 8) 6)
    (Transfer.deterministic 5 6) (Transfer.config 5 6 0 m) (2*bs.length+2) hhal
  have hf := hfirst (List.replicate k false) (by simp)
  have hf' : (List.replicate k false).foldl (fun c b => step (Transfer.program (5 : Fin 8) 6) b c)
      (Transfer.config 5 6 0 m)=⟨none,m₁⟩ := hf.2.trans hrun
  have h₅ : (m₁.push 6 false).stack 5=[] := by simpa [Memory.push] using hm₁.1
  let T := 2+(2*(bs.reverse.length+1)+2)
  refine ⟨k+T,m₂,?_,?_,hm₂.1,?_,?_,?_,?_⟩
  · simp only [T,List.length_reverse]; omega
  · simpa only [List.reverse_cons,List.reverse_reverse,h₅,List.append_nil] using hm₂.2.1
  · intro i hi hj
    exact (hm₂.2.2.1 i hj hi).trans ((show (m₁.push 6 false).stack i=m₁.stack i by simp [Memory.push,hj]).trans (hm₁.2.2.1 i hi hj))
  · exact hm₂.2.2.2.1.trans hm₁.2.2.2.1
  · exact hm₂.2.2.2.2.1.trans hm₁.2.2.2.2.1
  · intro coins hc
    rw [Sequence.deterministic_fold program (noCoin_deterministic program noCoin) _ _
      (List.replicate (k+T) false) (by simpa using hc),List.replicate_add]
    have he := Sequence.link_run (Transfer.program (5 : Fin 8) 6) back.labels back.start back.code
      (Transfer.config 5 6 0 m) (List.replicate k false) (List.replicate T false) hf.1
    rw [hf'] at he
    have hb := back_run bs.reverse m₁ hs6
    change (List.replicate k false++List.replicate T false).foldl (fun c b => step program b c)
      ⟨some program.start,m⟩=
      Sequence.right (Transfer.program (5 : Fin 8) 6) back.labels back.start back.code
        ((List.replicate T false).foldl (fun c b => step back b c) ⟨some back.start,m₁⟩) at he
    exact he.trans (congrArg (fun c : Config back =>
      Sequence.right (Transfer.program (5 : Fin 8) 6) back.labels back.start back.code c) hb)

end Contingency.BitModel.StackCode.HighPad

 

 

 

namespace Contingency.BitModel.StackCode.PreparedIntegerCall
noncomputable section

def outputRegister : Fin program.work := ⟨5,by decide⟩

theorem finite_memory_safe (N : ℕ) (rest xs : List Bool)
    (h : (xs.foldl (fun c b => step program b c)
      (initial program (encodeNat N++rest))).state=none) :
    ∃ u : Fin (N+1),
      (xs.foldl (fun c b => step program b c) (initial program (encodeNat N++rest))).memory.stack outputRegister=
        (IntegerDraw.integerWord N u).reverse ∧
      (xs.foldl (fun c b => step program b c) (initial program (encodeNat N++rest))).memory.input=rest ∧
      (xs.foldl (fun c b => step program b c) (initial program (encodeNat N++rest))).memory.outputRev=[] := by
  obtain ⟨t,ht,hr⟩ := refinement N rest
  let ys := xs++List.replicate t false
  have hl : (ys.take t).length=t := by simp [ys]
  obtain ⟨c,hc,hm,hi,ho⟩ := hr (ys.take t) hl (ys.drop t)
  rw [List.take_append_drop] at hc
  have he : ys.foldl (fun c b => step program b c) (initial program (encodeNat N++rest))=
      xs.foldl (fun c b => step program b c) (initial program (encodeNat N++rest)) := by
    unfold ys
    rw [List.foldl_append]
    exact Sequence.halted_fold program _ h _
  rw [he] at hc
  have ch : c.state=none := by
    have hh := h
    rw [hc] at hh
    exact Option.map_eq_none_iff.mp hh
  have ih : ((ys.drop t).foldl (fun c b => step IntegerDraw.program b c)
      (initial IntegerDraw.program (IntegerDraw.rawMaximum N))).state=none := by
    exact hm.1.symm.trans ch
  let b := ys.drop t
  have hh : (run IntegerDraw.program (IntegerDraw.rawMaximum N) b.get).state=none := by
    simpa only [run,List.ofFn_get] using ih
  obtain ⟨u,hu⟩ := IntegerDraw.stack_safe (IntegerDraw.rawMaximum N) b.get hh
  let v : Fin (N+1) := ⟨u,by simpa using u.isLt⟩
  refine ⟨v,?_,?_,?_⟩
  · rw [hc]
    change c.memory.stack 5=_
    apply hm.2.2.2.trans
    have hu' : (b.foldl (fun c b => step IntegerDraw.program b c)
        (initial IntegerDraw.program (IntegerDraw.rawMaximum N))).memory.outputRev.reverse=
          IntegerDraw.integerWord N v := by
      simpa only [run,List.ofFn_get,IntegerDraw.integerWord,IntegerDraw.validWord,v] using hu
    simpa only [List.reverse_reverse] using congrArg List.reverse hu'
  · rw [hc]; exact hi
  · rw [hc]; exact ho

end
end Contingency.BitModel.StackCode.PreparedIntegerCall

end

end OAI
