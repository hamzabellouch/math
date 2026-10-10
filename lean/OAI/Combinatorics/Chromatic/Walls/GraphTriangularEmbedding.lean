import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteLatticePairing
import OAI.Combinatorics.Chromatic.QuantumTorus.GraphRationalModel

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section

def rankedCell {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) (i:Fin n) :
    Cell (n+1+∑j,l j) :=
  ⟨⟨n+l i,by have H:=Finset.single_le_sum (f:=l) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i); omega⟩,
    ⟨(r i).rev.val,by change (r i).rev.val < n+l i+1; have H: (r i).rev.val < n:=(r i).rev.isLt; omega⟩⟩

lemma rankedCell_level {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) (i:Fin n) :
    (rankedCell l r i).1.val=n+l i := rfl
lemma rankedCell_row {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) (i:Fin n) :
    cellRow (rankedCell l r i)=(r i).rev.val := rfl
lemma rankedCell_injective {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) :
    Function.Injective (rankedCell l r) := by
  intro i j h
  have H:=congrArg cellRow h
  exact r.injective (Fin.rev_injective (Fin.ext H))
lemma rankedCell_phase {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) (i j:Fin n) :
    phaseEarlier (rankedCell l r i) (rankedCell l r j) ↔ r i < r j := by
  unfold phaseEarlier
  rw [rankedCell_row,rankedCell_row]
  have hrev: (r j).rev.val  <  (r i).rev.val ↔ r i < r j:=Fin.rev_lt_rev
  rw [hrev]
  constructor
  · rintro (h|⟨h,h'⟩)
    · exact h
    · have hij:=r.injective (Fin.rev_injective (Fin.ext h))
      subst j
      exact (lt_irrefl _ h').elim
  · exact Or.inl

lemma floor_pair_comparisons {x y:ℚ} (_hx:0≤x) (hy:0≤y) (hxy:x < y) :
    ⌊x⌋₊≤⌊y⌋₊ ∧
      (⌊x⌋₊=⌊y⌋₊ → x-(⌊x⌋₊:ℚ) < y-(⌊y⌋₊:ℚ)) ∧
      (⌊y⌋₊=⌊x⌋₊+1 → (y < x+1 ↔ y-(⌊y⌋₊:ℚ) < x-(⌊x⌋₊:ℚ))) ∧
      (⌊x⌋₊+2≤⌊y⌋₊ → x+1 < y) := by
  refine ⟨Nat.floor_mono (le_of_lt hxy),?_,?_,?_⟩
  · intro h
    rw [h]
    linarith
  · intro h
    rw [h,Nat.cast_add,Nat.cast_one]
    constructor  <;> intro H  <;> linarith
  · intro h
    have h':(⌊x⌋₊:ℚ)+2≤(⌊y⌋₊:ℚ):=by exact_mod_cast h
    linarith [Nat.lt_floor_add_one x,Nat.floor_le hy]

theorem graph_triangular_embedding {n:ℕ} (G:NaturalUnitIntervalGraph n) :
    ∃d:ℕ,∃b:Fin n ↪ Cell d,∀i j,i < j →
      bridgePositive (b j) (b i)=(if G.Edge i j then 1 else 0) ∧
      bridgePositive (b i) (b j)=0 := by
  obtain ⟨t,ht,hm,he⟩:=G.rational_model
  let l:Fin n → ℕ:=fun i=>⌊t i⌋₊
  let f:Fin n → ℚ:=fun i=>t i-(l i:ℚ)
  obtain ⟨r,hr⟩:=phase_rank f
  refine ⟨n+1+∑j,l j,⟨rankedCell l r,rankedCell_injective l r⟩,?_⟩
  intro i j hij
  have H:=floor_pair_comparisons (le_of_lt (ht i)) (le_of_lt (ht j)) (hm hij)
  change l i≤l j ∧ (l i=l j → f i < f j) ∧
    (l j=l i+1 → (t j < t i+1 ↔ f j < f i)) ∧ (l i+2≤l j → t i+1 < t j) at H
  have hedge:G.Edge i j ↔ j≤G.h i:=by
    simp only [NaturalUnitIntervalGraph.Edge,hij,true_and,not_lt_of_gt hij,false_and,or_false]
  have hclose:G.Edge i j ↔ t j < t i+1:=by
    rw [hedge]
    constructor
    · exact (he i j hij).1
    · intro hh
      by_contra hn
      linarith [(he i j hij).2 (lt_of_not_ge hn)]
  have heq:(rankedCell l r i).1=(rankedCell l r j).1 ↔ l i=l j:=by
    simp only [Fin.ext_iff,rankedCell_level,Nat.add_left_cancel_iff]
  have hnot:(rankedCell l r i).1.val+1≠(rankedCell l r j).1.val ↔ l i+1≠l j:=by
    simp only [rankedCell_level]; omega
  have hji: ¬((rankedCell l r j).1.val+1=(rankedCell l r i).1.val):=by
    simp only [rankedCell_level]
    omega
  by_cases hl:l i=l j
  · have hp:r i < r j:=(hr i j).mpr (Or.inl (H.2.1 hl))
    have htime:t j < t i+1:=by
      have hf0:0≤f i:=sub_nonneg.mpr (Nat.floor_le (le_of_lt (ht i)))
      have hf1:f j < 1:=by dsimp [f,l]; linarith [Nat.lt_floor_add_one (t j)]
      dsimp [f] at hf0 hf1
      rw [←hl] at hf1
      linarith
    have hed:=hclose.mpr htime
    constructor
    · simp [bridgePositive,rankedCell_phase,(heq.mpr hl).symm,hp,hed]
    · simp [bridgePositive,rankedCell_phase,heq.mpr hl,not_lt_of_gt hp]
  · have hl':l i < l j:=lt_of_le_of_ne H.1 hl
    have hpnot:¬(rankedCell l r j).1=(rankedCell l r i).1:=by
      intro he'; exact hl (heq.mp he'.symm)
    have hsmall:¬(rankedCell l r i).1=(rankedCell l r j).1:=by
      intro he'; exact hl (heq.mp he')
    constructor
    · rw [bridgePositive,ite_eq_right (by simp [hpnot])]
      have hequiv: (rankedCell l r i).1.val+1=(rankedCell l r j).1.val ∧
          phaseEarlier (rankedCell l r j) (rankedCell l r i) ↔ G.Edge i j:=by
        rw [rankedCell_phase,rankedCell_level,rankedCell_level,hclose]
        constructor
        · rintro ⟨hl1,hp⟩
          have hll:l j=l i+1:=by omega
          rcases (hr j i).mp hp with hf|⟨_,hji'⟩
          · exact (H.2.2.1 hll).mpr hf
          · exact (lt_asymm hij hji').elim
        · intro hh
          have hll:l j=l i+1:=by
            by_contra hn
            have hh':l i+2≤l j:=by omega
            linarith [H.2.2.2 hh']
          refine ⟨by omega,(hr j i).mpr (Or.inl ((H.2.2.1 hll).mp hh))⟩
      change (if (rankedCell l r i).1.val+1=(rankedCell l r j).1.val ∧
        phaseEarlier (rankedCell l r j) (rankedCell l r i) then (1:ℤ) else 0)=_
      simp only [hequiv]
    · simp [bridgePositive,hsmall,hji]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
