import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularGaps
import OAI.Combinatorics.Chromatic.Walls.TriangularGapPairing

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma levelTotal_node (i j:Fin n) (t:Fin (j.val+3)) :
    levelTotal cellLevel i (Pi.single (levelNode j t) (1:ℤ))=
      if j=i ∧ 0<t.val ∧ t.val<j.val+2 then 1 else 0 := by
  unfold levelNode
  by_cases h0:t.val=0
  · rw [dite_eq_left h0]
    change levelTotal cellLevel i (anchor j.castSucc)=_
    rw [levelTotal_anchor]
    simp only [h0,lt_self_iff_false,false_and,and_false,ite_false]
  · rw [dite_eq_right h0]
    by_cases he:t.val=j.val+2
    · rw [dite_eq_left he]
      change levelTotal cellLevel i (anchor j.succ)=_
      rw [levelTotal_anchor]
      simp only [he,lt_self_iff_false,and_false,ite_false]
    · rw [dite_eq_right he]
      change levelTotal cellLevel i (bridge ⟨j,⟨j.val+1-t.val,_⟩⟩)=_
      rw [levelTotal_bridge]
      have h1:0<t.val:=by omega
      have h2:t.val<j.val+2:=by have := t.isLt; omega
      simp only [cellLevel,h1,h2,and_true]
      rfl

lemma levelTotal_gap (i:Fin n) (g:GapIndex n) :
    levelTotal cellLevel i (forwardGap g)=
      (if g.1=i ∧ g.2.val=0 then 1 else 0)-
      (if g.1=i ∧ g.2.val=g.1.val+1 then 1 else 0) := by
  rw [forwardGap,map_sub,levelTotal_node,levelTotal_node]
  simp only [Fin.val_succ,Fin.val_castSucc]
  have hg:=g.2.isLt
  by_cases hi:g.1=i
  · simp only [hi,true_and]
    split_ifs <;> omega
  · simp only [hi,false_and,ite_false,sub_self]

lemma levelTotal_roots (i:Fin n) (c:GapIndex n → ℤ) :
    levelTotal cellLevel i (forwardRoots c)=gapValue c (i.val+1) 0-gapValue c (i.val+1) (i.val+1) := by
  rw [forwardRoots_apply,map_sum]
  simp only [map_zsmul,smul_eq_mul,levelTotal_gap,gapValue,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have h1:g.1.val+1=i.val+1 ↔ g.1=i := by simp [Fin.ext_iff]
  by_cases he:g.1=i
  · simp only [he,true_and,mul_sub,mul_ite,mul_one,mul_zero]
  · simp only [h1,he,false_and,ite_false,sub_self,mul_zero]

lemma gapValue_end_eq (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0) (i:ℕ) :
    gapValue c i 0=gapValue c i i := by
  by_cases hi:1 ≤ i ∧ i ≤ n
  · let a:Fin n:=⟨i-1,by omega⟩
    have H:=hK a
    rw [hm,map_add,levelTotal_anchor,zero_add,levelTotal_roots] at H
    have ha:a.val+1=i:=by dsimp [a]; omega
    rw [ha] at H
    omega
  · rw [gapValue_out c i 0 (by omega),gapValue_out c i i (by omega)]
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def gapU (c:GapIndex n → ℤ) (j i:ℕ) : ℤ :=
  if 1 ≤ j ∧ j ≤ i ∧ i ≤ n then gapValue c i (i+1-j) else 0

def indexedCell (j i:ℕ) (h:1 ≤ j ∧ j ≤ i ∧ i ≤ n) : Cell n :=
  ⟨⟨i-1,by omega⟩,⟨j-1,by change j-1 < i-1+1; omega⟩⟩

def gapXi (m:Lattice n (Cell n)) (j i:ℕ) : ℤ :=
  if h:1 ≤ j ∧ j ≤ i ∧ i ≤ n then triangularOmega n (eventRoot cellLevel 0 (indexedCell j i h)) m else 0

lemma gapU_first (c:GapIndex n → ℤ) (i:ℕ) : gapU c 1 i=gapValue c i i := by
  unfold gapU
  by_cases h:1 ≤ 1 ∧ 1 ≤ i ∧ i ≤ n
  · rw [ite_eq_left h,Nat.add_sub_cancel]
  · rw [ite_eq_right h,gapValue_out c i i (by omega)]

lemma gapU_upper (c:GapIndex n → ℤ) (j i:ℕ) (hj:1 ≤ j) (hji:j ≤ i) :
    gapU c (j+1) (i+1)=gapValue c (i+1) (i+1-j) := by
  unfold gapU
  by_cases h:1 ≤ j+1 ∧ j+1 ≤ i+1 ∧ i+1 ≤ n
  · rw [ite_eq_left h]
    congr 1
    omega
  · rw [ite_eq_right h,gapValue_out c (i+1) (i+1-j) (by omega)]

lemma gapXi_formula (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (j i:ℕ) (hj:1 ≤ j) (hji:j ≤ i) (hi:i ≤ n) :
    gapXi m j i=(if i=1 then 1 else 0)-gapValue c i (i+1-j)-gapValue c i (i-j)+
      gapValue c (i-1) (i-j)+gapValue c (i+1) (i+1-j) := by
  have hh:1 ≤ j ∧ j ≤ i ∧ i ≤ n:=⟨hj,hji,hi⟩
  rw [gapXi,dite_eq_left hh,hm,map_add,eventRoot_anchor,eventRoot_roots,sum_eventGapWeight]
  simp only [indexedCell,Fin.ext_iff,Fin.val_zero,Fin.val_castSucc,Fin.val_succ]
  have h1:i-1+1=i:=by omega
  have h2:i-1-(j-1)=i-j:=by omega
  have h3:i-1+1-(j-1)=i+1-j:=by omega
  have h4:i-1+2=i+1:=by omega
  have hz:¬0=i-1+1:=by omega
  have hzi:0=i-1 ↔ i=1:=by omega
  rw [h2,h3,h4]
  have hze:¬0=i:=by omega
  simp only [hzi,h1,hze,ite_false,sub_zero]
  rw [gapValue_end_eq c m hm hK i,gapValue_end_eq c m hm hK (i-1)]
  ring

lemma gapXi_pairing (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (j i:ℕ) (hj:1 ≤ j) (hji:j ≤ i) (hi:i ≤ n) :
    gapXi m j i=(if i=1 then 1 else 0)-gapU c j i-
      (if j < i then gapU c (j+1) i else gapU c 1 i)+
      (if j < i then gapU c j (i-1) else gapU c 1 (j-1))+gapU c (j+1) (i+1) := by
  rw [gapXi_formula c m hm hK j i hj hji hi,gapU_upper c j i hj hji]
  have hu:gapU c j i=gapValue c i (i+1-j):=by rw [gapU,ite_eq_left ⟨hj,hji,hi⟩]
  rw [hu]
  by_cases hji':j < i
  · have hU1:gapU c (j+1) i=gapValue c i (i-j):=by
      rw [gapU,ite_eq_left (show 1 ≤ j+1 ∧ j+1 ≤ i ∧ i ≤ n by omega)]
      congr 1
      omega
    have hU2:gapU c j (i-1)=gapValue c (i-1) (i-j):=by
      rw [gapU,ite_eq_left (show 1 ≤ j ∧ j ≤ i-1 ∧ i-1 ≤ n by omega)]
      congr 1
      omega
    rw [ite_eq_left hji',ite_eq_left hji',hU1,hU2]
  · have hjj:j=i:=by omega
    subst j
    rw [ite_eq_right (lt_irrefl i),ite_eq_right (lt_irrefl i),gapU_first,gapU_first,Nat.sub_self,
      gapValue_end_eq c m hm hK i,gapValue_end_eq c m hm hK (i-1)]

def actualIntegerGaps (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hc:∀g,0 ≤ c g) (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (hxi:∀b,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) m) : TriangularGaps.IntegerGaps n where
  u:=gapU c
  xi:=gapXi m
  u_out j i h:=by rw [gapU,ite_eq_right h]
  u_nonneg j i:=by unfold gapU; split_ifs; exact gapValue_nonneg c hc _ _; omega
  xi_nonneg j i hj hji hi:=by rw [gapXi,dite_eq_left ⟨hj,hji,hi⟩]; exact hxi _
  pairing:=gapXi_pairing c m hm hK
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
