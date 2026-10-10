import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.Admissible
import OAI.Combinatorics.Chromatic.Histories.ColorBlockEnergy

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
open Classical
noncomputable section

lemma ordered_pair_sum {n:ℕ} (f:Fin n → Fin n → ℤ) (hf:∀i,f i i=0) :
    (∑i:Fin n,∑j:Fin n,f i j) = ∑i:Fin n,∑j:Fin n,if i < j then f i j+f j i else 0 := by
  have H:(∑i:Fin n,∑j:Fin n,f i j)=(∑i:Fin n,∑j:Fin n,if i < j then f i j else 0)+(∑i:Fin n,∑j:Fin n,if j < i then f i j else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [hf]
    · simp [h,not_lt_of_gt h]
  rw [H,Finset.sum_comm (f:=fun i j=>if j < i then f i j else 0),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

namespace NaturalUnitIntervalGraph
open QuantumTorus
variable {n r:ℕ} (G:NaturalUnitIntervalGraph n)
variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (u:V → M) (b:Fin n ↪ V)
variable (hp:∀i j,i < j → Ω (u (b i)) (u (b j))= -(if G.Edge i j then 1 else 0))

include hΩ hp in
omit [Fintype V] [DecidableEq V] in
lemma pairing_zero_iff (i j:Fin n) : Ω (u (b i)) (u (b j))=0 ↔ ¬G.Edge i j := by
  rcases lt_trichotomy i j with h|h|h
  · rw [hp i j h]
    by_cases he:G.Edge i j <;> simp [he]
  · subst j; simp [hΩ]
  · rw [QuantumTorus.alternating_skew Ω hΩ, hp j i h,G.edge_comm i j]
    simp

include hΩ hp in
omit [Fintype V] [DecidableEq V] in
lemma independent_blocks_iff (κ:Fin n → Fin r) :
    (∀c,IsIndependent Ω u (SquarefreeBlocks.blocks b κ c)) ↔ G.Proper κ := by
  constructor
  · intro h i j he heq
    have H:=h (κ i) (b i) ((SquarefreeBlocks.mem_blocks b κ _ _).mpr ⟨i,rfl,rfl⟩)
      (b j) ((SquarefreeBlocks.mem_blocks b κ _ _).mpr ⟨j,heq.symm,rfl⟩)
    exact ((G.pairing_zero_iff Ω hΩ u b hp i j).mp H) he
  · intro h c x hx y hy
    obtain ⟨i,hi,rfl⟩:=(SquarefreeBlocks.mem_blocks b κ c x).mp hx
    obtain ⟨j,hj,rfl⟩:=(SquarefreeBlocks.mem_blocks b κ c y).mp hy
    apply (G.pairing_zero_iff Ω hΩ u b hp i j).mpr
    exact fun he=>h i j he (hi.trans hj.symm)

include hΩ hp in
omit [Fintype V] [DecidableEq V] in
lemma blockValid_iff (κ:Fin n → Fin r) (a:Fin r → ℕ) :
    BlockValid Ω u a (SquarefreeBlocks.blocks b κ) ↔
      G.Proper κ ∧ ∀c,(Finset.univ.filter (fun i=>κ i=c)).card=a c := by
  rw [BlockValid,forall_and,G.independent_blocks_iff Ω hΩ u b hp]
  simp only [SquarefreeBlocks.blocks,Finset.card_map]

include hΩ hp in
omit [Fintype V] [DecidableEq V] in
lemma blocks_energy (κ:Fin n → Fin r) (hκ:G.Proper κ) :
    wordEnergy Ω (blockLabels u (SquarefreeBlocks.blocks b κ))=
      2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ) := by
  rw [wordEnergy_blocks,ordered_pair_sum _ (by intro i; simp)]
  have H:∀i j:Fin n,(if i < j then
      (if κ i<κ j then Ω (u (b i)) (u (b j)) else 0)+
      (if κ j<κ i then Ω (u (b j)) (u (b i)) else 0) else 0)=
      (if i < j ∧ G.Edge i j ∧ κ j<κ i then (1:ℤ) else 0)-
      (if i < j ∧ G.Edge i j ∧ κ i<κ j then (1:ℤ) else 0) := by
    intro i j
    by_cases hij:i < j
    · rw [ite_eq_left hij,QuantumTorus.alternating_skew Ω hΩ (u (b j)) (u (b i)),hp i j hij]
      by_cases he:G.Edge i j
      · rcases lt_or_gt_of_ne (hκ i j he) with h|h
        · simp [hij,he,h,not_lt_of_gt h]
        · simp [hij,he,h,not_lt_of_gt h]
      · simp [hij,he]
    · simp [hij]
  simp only [H,Finset.sum_sub_distrib]
  have hi:(G.coloringInversions κ:ℤ)=
      ∑i:Fin n,∑j:Fin n,if i < j ∧ G.Edge i j ∧ κ j<κ i then (1:ℤ) else 0 := by
    simp only [coloringInversions,edges,Finset.filter_filter,Finset.card_eq_sum_ones,
      Nat.cast_sum,Finset.sum_filter,Fintype.sum_prod_type,apply_ite,Nat.cast_one,Nat.cast_zero]
    congr 2
    funext i
    congr 1
    funext j
    simp [and_assoc]
  have ha:(G.coloringAscents κ:ℤ)=
      ∑i:Fin n,∑j:Fin n,if i < j ∧ G.Edge i j ∧ κ i<κ j then (1:ℤ) else 0 := by
    simp only [coloringAscents,Finset.card_eq_sum_ones,
      Nat.cast_sum,Finset.sum_filter,Fintype.sum_prod_type,apply_ite,Nat.cast_one,Nat.cast_zero]
  rw [←hi,←ha]
  have hc: (G.coloringInversions κ:ℤ)+(G.coloringAscents κ:ℤ)=(G.edgeCount:ℤ):=by
    exact_mod_cast G.coloringInversions_add_ascents κ hκ
  omega
end NaturalUnitIntervalGraph
end
end ElementaryPositivity

end

end OAI
