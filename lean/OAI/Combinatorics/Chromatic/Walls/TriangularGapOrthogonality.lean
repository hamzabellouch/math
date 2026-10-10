import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularGapTotals

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma stationary_anchor_pair_zero (m:Lattice n (Cell n)) (hK:∀i,levelTotal cellLevel i m=0)
    (a:Fin (n+1)) : triangularOmega n (anchor a) m=0 := by
  have HT:∀i,extendedTotal cellLevel m i=0 := by
    intro i
    unfold extendedTotal
    split_ifs <;> first | exact hK _ | rfl
  change chartPairing cellLevel triangularBB (anchor a) m=0
  rw [chartPairing_anchor,HT,HT,sub_self]

lemma gapXi_cell (m:Lattice n (Cell n)) (b:Cell n) :
    gapXi m (b.2.val+1) (b.1.val+1)=triangularOmega n (eventRoot cellLevel 0 b) m := by
  have hb:=b.2.isLt
  rw [gapXi,dite_eq_left (by have hn:=b.1.isLt; omega)]
  congr 2

lemma gap_positive_u (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (g:GapIndex n) (hg:0 < c g) :
    ∃j,1 ≤ j ∧ j ≤ g.1.val+1 ∧ 0 < gapU c j (g.1.val+1) := by
  have ht:=g.2.isLt
  by_cases hz:g.2.val=0
  · refine ⟨1,by omega,by omega,?_⟩
    rw [gapU_first,←gapValue_end_eq c m hm hK,←hz,gapValue_read]
    exact hg
  · let j:=g.1.val+2-g.2.val
    have hj:1 ≤ j ∧ j ≤ g.1.val+1 ∧ g.1.val+1 ≤ n := by
      have hn:=g.1.isLt
      dsimp [j]
      omega
    refine ⟨j,hj.1,hj.2.1,?_⟩
    rw [gapU,ite_eq_left hj]
    have he:g.1.val+1+1-j=g.2.val:=by dsimp [j]; omega
    rw [he,gapValue_read]
    exact hg

lemma positive_level_event_zero (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hc:∀g,0 ≤ c g) (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (hxi:∀b,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) m)
    (g:GapIndex n) (hg:0 < c g) (b:Cell n) (hbg:b.1=g.1) :
    triangularOmega n (eventRoot cellLevel 0 b) m=0 := by
  obtain ⟨j,hj,hji,hu⟩:=gap_positive_u c m hm hK g hg
  let A:=actualIntegerGaps c m hc hm hK hxi
  have H:=A.positive_gap_zero_pairings j (g.1.val+1) hj hji (by have := g.1.isLt; omega) hu
    (b.2.val+1) (by omega) (by have hb:=b.2.isLt; have he:=congrArg Fin.val hbg; omega)
  change gapXi m (b.2.val+1) (g.1.val+1)=0 at H
  rw [←hbg,gapXi_cell] at H
  exact H

lemma positive_gap_target_zero (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hc:∀g,0 ≤ c g) (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (hxi:∀b,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) m)
    (g:GapIndex n) (hg:0 < c g) : triangularOmega n (forwardGap g) m=0 := by
  have HB:∀b:Cell n,b.1=g.1 → triangularOmega n (bridge b) m=0 := by
    intro b hb
    have H:=positive_level_event_zero c m hc hm hK hxi g hg b hb
    simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,AddMonoidHom.sub_apply,
      stationary_anchor_pair_zero m hK,sub_zero] at H
    exact H
  have HN:∀t:Fin (g.1.val+3),triangularOmega n (Pi.single (levelNode g.1 t) 1) m=0 := by
    intro t
    unfold levelNode
    split_ifs
    · exact stationary_anchor_pair_zero m hK _
    · exact stationary_anchor_pair_zero m hK _
    · exact HB _ rfl
  rw [forwardGap,map_sub,AddMonoidHom.sub_apply,HN,HN,sub_self]
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

lemma phaseEarlier_trans {a b c : Cell n} (hab : phaseEarlier a b) (hbc : phaseEarlier b c) :
    phaseEarlier a c := by
  unfold phaseEarlier at *
  rcases hab with hab|⟨hab,hab'⟩ <;> rcases hbc with hbc|⟨hbc,hbc'⟩
  · left; omega
  · left; omega
  · left; omega
  · right; exact ⟨hab.trans hbc,lt_trans hab' hbc'⟩

def phaseLE (a b : Cell n) : Prop := phaseEarlier a b ∨ a=b
instance : DecidableRel (@phaseLE n) := fun _ _=>inferInstanceAs (Decidable (_ ∨ _))
instance : IsTrans (Cell n) phaseLE where
  trans a b c hab hbc := by
    rcases hab with hab|rfl
    · rcases hbc with hbc|rfl
      · exact Or.inl (phaseEarlier_trans hab hbc)
      · exact Or.inl hab
    · exact hbc
instance : Std.Antisymm (@phaseLE n) where
  antisymm a b hab hba := by
    rcases hab with hab|h
    · rcases hba with hba|h
      · exact (phaseEarlier_asymm hab hba).elim
      · exact h.symm
    · exact h
instance : Std.Total (@phaseLE n) where
  total a b := by
    rcases phaseEarlier_trichotomy a b with h|h|h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)

def phaseCycle (n : ℕ) : List (Cell n) := Finset.univ.sort phaseLE
@[simp] lemma mem_phaseCycle (b : Cell n) : b∈phaseCycle n := by simp [phaseCycle]
lemma phaseCycle_nodup : (phaseCycle n).Nodup := Finset.sort_nodup _ _
lemma phaseCycle_pairwise : (phaseCycle n).Pairwise phaseLE := by
  exact Finset.pairwise_sort _ _

lemma prefix_before {pre post : List (Cell n)} {b c : Cell n}
    (hcycle : phaseCycle n=pre++b::post) : c∈pre ↔ phaseEarlier c b := by
  have hp:=phaseCycle_pairwise (n:=n)
  rw [hcycle] at hp
  have hnd:=phaseCycle_nodup (n:=n)
  rw [hcycle] at hnd
  have hneq : b∉pre := by
    have H:=(List.nodup_append.mp hnd).2.2
    exact fun hb=>H b hb b (by simp) rfl
  constructor
  · intro hc
    have hh:phaseLE c b:=(List.pairwise_append.mp hp).2.2 c hc b (by simp)
    rcases hh with hh|hh
    · exact hh
    · subst c; exact (hneq hc).elim
  · intro hcb
    have hc:=mem_phaseCycle c
    rw [hcycle,List.mem_append,List.mem_cons] at hc
    rcases hc with hc|hc|hc
    · exact hc
    · subst c; exact (phaseEarlier_irrefl b hcb).elim
    · have hh:phaseLE b c:=(List.pairwise_cons.mp (List.pairwise_append.mp hp).2.1).1 c hc
      rcases hh with hh|hh
      · exact (phaseEarlier_asymm hcb hh).elim
      · subst c; exact (phaseEarlier_irrefl b hcb).elim
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
