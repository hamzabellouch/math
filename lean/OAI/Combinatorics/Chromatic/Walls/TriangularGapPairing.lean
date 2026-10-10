import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PathRoot

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def ownNodeWeight (a r j:ℕ) : ℤ :=
  if j=0 then 1 else if j=a+2 then -1 else
    if j+r < a+1 then 2 else if j+r=a+1 then 1 else 0
def lowerNodeWeight (a r j:ℕ) : ℤ :=
  if j=0 then 0 else if j=a+2 then 1 else if j+r ≤ a+1 then -1 else 0
def upperNodeWeight (a r j:ℕ) : ℤ :=
  if j=0 then -1 else if j=a+2 then 0 else if j+r < a+1 then -1 else 0

def eventNodeWeight (b:Cell n) (i:Fin n) (j:ℕ) : ℤ :=
  if i=b.1 then ownNodeWeight i.val b.2.val j
  else if i.val+1=b.1.val then lowerNodeWeight i.val b.2.val j
  else if b.1.val+1=i.val then upperNodeWeight i.val b.2.val j
  else 0

lemma eventRoot_levelNode (b:Cell n) (i:Fin n) (j:Fin (i.val+3)) :
    triangularOmega n (eventRoot cellLevel 0 b) (Pi.single (levelNode i j) 1)=eventNodeWeight b i j.val := by
  have hb := b.2.isLt
  have hj := j.isLt
  unfold levelNode
  split_ifs with h0 he
  · change triangularOmega n (eventRoot cellLevel 0 b) (anchor i.castSucc)=_
    rw [eventRoot_anchor]
    simp only [eventNodeWeight,ownNodeWeight,lowerNodeWeight,upperNodeWeight,h0,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
    split_ifs <;> first | contradiction | omega
  · change triangularOmega n (eventRoot cellLevel 0 b) (anchor i.succ)=_
    rw [eventRoot_anchor]
    simp only [eventNodeWeight,ownNodeWeight,lowerNodeWeight,upperNodeWeight,he,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
    split_ifs <;> first | contradiction | omega
  · change triangularOmega n (eventRoot cellLevel 0 b) (bridge ⟨i,⟨i.val+1-j.val,_⟩⟩)=_
    rw [eventRoot_bridge_value]
    have hcell : (⟨i,⟨i.val+1-j.val,by omega⟩⟩ : Cell n)=b ↔
        i.val=b.1.val ∧ i.val+1-j.val=b.2.val := by
      constructor
      · intro h; exact ⟨congrArg (fun x:Cell n=>x.1.val) h,congrArg (fun x:Cell n=>x.2.val) h⟩
      · intro h; exact cell_ext (Fin.ext h.1) h.2
    simp only [hcell,eventNodeWeight,ownNodeWeight,lowerNodeWeight,upperNodeWeight,phaseEarlier,cellRow,Fin.ext_iff,Fin.lt_def]
    by_cases hlev:i.val=b.1.val
    · simp only [hlev,ite_true,true_and,lt_self_iff_false,and_false,or_false]
      split_ifs <;> first | contradiction | omega
    · simp only [hlev,ite_false]
      by_cases hlo:i.val+1=b.1.val
      · simp only [hlo,true_or,ite_true]
        split_ifs <;> first | contradiction | omega
      · simp only [hlo,false_or,ite_false]
        by_cases hup:b.1.val+1=i.val
        · simp only [hup,ite_true]
          split_ifs <;> first | contradiction | omega
        · simp only [hup,ite_false]

lemma ownNodeWeight_step (a r j:ℕ) (hr:r ≤ a) (hj:j ≤ a+1) :
    ownNodeWeight a r (j+1)-ownNodeWeight a r j=
      (if j=0 then 1 else 0)-(if j=a-r then 1 else 0)-
      (if j=a+1-r then 1 else 0)-(if j=a+1 then 1 else 0) := by
  have h1 : j=a-r ↔ j+r=a := by omega
  have h2 : j=a+1-r ↔ j+r=a+1 := by omega
  simp only [ownNodeWeight,h1,h2]
  by_cases hz:j=0
  · simp only [hz,zero_add]
    split_ifs <;> first | contradiction | omega
  · simp only [hz,ite_false]
    by_cases he:j=a+1
    · simp only [he]
      split_ifs <;> first | contradiction | omega
    · split_ifs <;> first | contradiction | omega

lemma lowerNodeWeight_step (a r j:ℕ) (hr:r ≤ a+1) (hj:j ≤ a+1) :
    lowerNodeWeight a r (j+1)-lowerNodeWeight a r j=
      -(if j=0 then 1 else 0)+(if j=a+1-r then 1 else 0)+
      (if j=a+1 then 1 else 0) := by
  have h1:j=a+1-r ↔ j+r=a+1 := by omega
  simp only [lowerNodeWeight,h1]
  by_cases hz:j=0
  · simp only [hz,zero_add]
    split_ifs <;> first | contradiction | omega
  · simp only [hz,ite_false]
    by_cases he:j=a+1
    · simp only [he]
      split_ifs <;> first | contradiction | omega
    · split_ifs <;> first | contradiction | omega

lemma upperNodeWeight_step (a r j:ℕ) (hr:r < a) (hj:j ≤ a+1) :
    upperNodeWeight a r (j+1)-upperNodeWeight a r j=
      (if j=a-r then 1 else 0) := by
  have h1:j=a-r ↔ j+r=a := by omega
  simp only [upperNodeWeight,h1]
  split_ifs <;> first | contradiction | omega

def eventGapWeight (b:Cell n) (g:GapIndex n) : ℤ :=
  if g.1=b.1 then
    (if g.2.val=0 then 1 else 0) -
    (if g.2.val=b.1.val-b.2.val then 1 else 0) -
    (if g.2.val=b.1.val+1-b.2.val then 1 else 0) -
    (if g.2.val=b.1.val+1 then 1 else 0)
  else if g.1.val+1=b.1.val then
    -(if g.2.val=0 then 1 else 0) +
    (if g.2.val=b.1.val-b.2.val then 1 else 0) +
    (if g.2.val=b.1.val then 1 else 0)
  else if b.1.val+1=g.1.val then
    (if g.2.val=b.1.val+1-b.2.val then 1 else 0)
  else 0

lemma eventRoot_forwardGap (b:Cell n) (g:GapIndex n) :
    triangularOmega n (eventRoot cellLevel 0 b) (forwardGap g)=eventGapWeight b g := by
  rw [forwardGap,map_sub,eventRoot_levelNode,eventRoot_levelNode]
  simp only [Fin.val_succ,Fin.val_castSucc,eventNodeWeight,eventGapWeight,Fin.ext_iff]
  have hb:=b.2.isLt
  have hg:=g.2.isLt
  by_cases hlev:g.1.val=b.1.val
  · simp only [hlev,ite_true]
    exact ownNodeWeight_step _ _ _ (by omega) (by omega)
  · simp only [hlev,ite_false]
    by_cases hlo:g.1.val+1=b.1.val
    · simp only [hlo,ite_true]
      convert lowerNodeWeight_step g.1.val b.2.val g.2.val (by omega) (by omega) using 1
      rw [hlo]
    · simp only [hlo,ite_false]
      by_cases hup:b.1.val+1=g.1.val
      · simp only [hup,ite_true]
        convert upperNodeWeight_step g.1.val b.2.val g.2.val (by omega) (by omega) using 1
      · simp only [hup,ite_false,sub_self]
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def gapValue (c:GapIndex n → ℤ) (i t:ℕ) : ℤ :=
  ∑g,if g.1.val+1=i ∧ g.2.val=t then c g else 0

lemma gapValue_nonneg (c:GapIndex n → ℤ) (hc:∀g,0 ≤ c g) (i t:ℕ) : 0 ≤ gapValue c i t := by
  apply Finset.sum_nonneg
  intro g _
  split_ifs <;> first | exact hc g | omega

lemma gapValue_out (c:GapIndex n → ℤ) (i t:ℕ)
    (h:¬(1 ≤ i ∧ i ≤ n ∧ t ≤ i)) : gapValue c i t=0 := by
  apply Finset.sum_eq_zero
  intro g _
  split_ifs with hg
  · have h1:=g.1.isLt
    have h2:=g.2.isLt
    exact (h (by omega)).elim
  · rfl

lemma gap_ext (g f:GapIndex n) (h1:g.1.val=f.1.val) (h2:g.2.val=f.2.val) : g=f := by
  cases g with | mk i g =>
    cases f with | mk j f =>
      have hij:i=j:=Fin.ext h1
      subst j
      have hgf:g=f:=Fin.ext h2
      subst f
      rfl

lemma gapValue_read (c:GapIndex n → ℤ) (g:GapIndex n) : gapValue c (g.1.val+1) g.2.val=c g := by
  rw [gapValue,Finset.sum_eq_single g]
  · simp
  · intro f _ hfg
    have hf:¬(f.1.val+1=g.1.val+1 ∧ f.2.val=g.2.val) := by
      intro h
      exact hfg (gap_ext f g (by omega) h.2)
    simp only [hf,ite_false]
  · simp

lemma sum_eventGapWeight (c:GapIndex n → ℤ) (b:Cell n) :
    (∑g,c g*eventGapWeight b g)=
      gapValue c (b.1.val+1) 0-gapValue c (b.1.val+1) (b.1.val-b.2.val)-
      gapValue c (b.1.val+1) (b.1.val+1-b.2.val)-gapValue c (b.1.val+1) (b.1.val+1)-
      gapValue c b.1.val 0+gapValue c b.1.val (b.1.val-b.2.val)+gapValue c b.1.val b.1.val+
      gapValue c (b.1.val+2) (b.1.val+1-b.2.val) := by
  simp only [gapValue,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have h1:g.1.val+1=b.1.val+1 ↔ g.1.val=b.1.val := by omega
  have h2:g.1.val+1=b.1.val+2 ↔ b.1.val+1=g.1.val := by omega
  simp only [eventGapWeight,Fin.ext_iff,h1,h2]
  by_cases he:g.1.val=b.1.val
  · have hlo:g.1.val+1≠b.1.val:=by omega
    have hup:b.1.val+1≠g.1.val:=by omega
    have hself:b.1.val+1≠b.1.val:=by omega
    simp only [he,hself,true_and,false_and,ite_true,ite_false,mul_sub,mul_ite,mul_one,mul_zero]
    ring
  · by_cases hlo:g.1.val+1=b.1.val
    · have hup:b.1.val+1≠g.1.val:=by omega
      simp only [he,hlo,hup,true_and,false_and,ite_true,ite_false,mul_add,mul_neg,mul_ite,mul_one,mul_zero]
      ring
    · by_cases hup:b.1.val+1=g.1.val
      · simp only [he,hlo,hup,true_and,false_and,ite_true,ite_false,mul_ite,mul_one,mul_zero]
        ring
      · simp only [he,hlo,hup,false_and,ite_false,mul_zero,sub_zero,add_zero]

lemma eventRoot_roots (b:Cell n) (c:GapIndex n → ℤ) :
    triangularOmega n (eventRoot cellLevel 0 b) (forwardRoots c)=∑g,c g*eventGapWeight b g := by
  rw [forwardRoots_apply,map_sum]
  simp only [map_zsmul,smul_eq_mul,eventRoot_forwardGap]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
