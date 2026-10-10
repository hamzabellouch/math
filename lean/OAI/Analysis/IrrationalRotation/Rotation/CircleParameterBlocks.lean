import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace OAI

namespace Invariant233.CircleParameterData

@[simp] theorem blockEnd_zero (p : CircleParameterData) : p.blockEnd 0 = 0 := by
  simp [blockEnd]

theorem blockEnd_succ (p : CircleParameterData) (j : ℕ) :
    p.blockEnd (j + 1) = p.blockEnd j + p.m (j + 1) := by
  exact Finset.sum_Icc_succ_top (by omega) p.m

theorem card_block (p : CircleParameterData) (j : ℕ) (hj : 1 ≤ j) :
    (p.block j).card = p.m j := by
  have hd := p.blockEnd_succ (j - 1)
  have he : j - 1 + 1 = j := by omega
  rw [he] at hd
  simp only [block, Nat.card_Icc]
  omega

theorem mem_block_iff (p : CircleParameterData) (j i : ℕ) :
    i ∈ p.block j ↔ p.blockEnd (j - 1) < i ∧ i ≤ p.blockEnd j := by
  simp only [block, Finset.mem_Icc, Nat.add_one_le_iff]

theorem blockEnd_ge_index (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (j : ℕ) : j ≤ p.blockEnd j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [blockEnd_succ]
    have h := hm (j + 1) (by omega)
    omega

theorem blockEnd_strictMono (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) : StrictMono p.blockEnd := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [blockEnd_succ]
  exact Nat.lt_add_of_pos_right (hm (j + 1) (by omega))

theorem exists_mem_block (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (i : ℕ) (hi : 1 ≤ i) :
    ∃ j, 1 ≤ j ∧ i ∈ p.block j := by
  have hex : ∃ j, i ≤ p.blockEnd j := ⟨i, p.blockEnd_ge_index hm i⟩
  let j := Nat.find hex
  have hj : i ≤ p.blockEnd j := Nat.find_spec hex
  have hjpos : 1 ≤ j := by
    by_contra h
    have he : j = 0 := by omega
    rw [he, blockEnd_zero] at hj
    omega
  refine ⟨j, hjpos, (p.mem_block_iff j i).mpr ⟨?_, hj⟩⟩
  have hprev : ¬ i ≤ p.blockEnd (j - 1) :=
    Nat.find_min hex (show j - 1 < j by omega)
  omega

theorem block_index_unique (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {j k i : ℕ}
    (hij : i ∈ p.block j) (hik : i ∈ p.block k) : j = k := by
  have hj := (p.mem_block_iff j i).mp hij
  have hk := (p.mem_block_iff k i).mp hik
  have hmono := (p.blockEnd_strictMono hm).monotone
  apply le_antisymm
  · by_contra h
    have hjk : k ≤ j - 1 := by omega
    have hd := hmono hjk
    omega
  · by_contra h
    have hjk : j ≤ k - 1 := by omega
    have hd := hmono hjk
    omega

theorem blockIndex_eq_of_mem (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {j i : ℕ} (hi : i ∈ p.block j) :
    p.blockIndex i = j := by
  classical
  have hij := (p.mem_block_iff j i).mp hi
  have hex : ∃ k, i ≤ p.blockEnd k := ⟨j, hij.2⟩
  rw [blockIndex, dite_eq_left hex]
  apply le_antisymm
  · exact Nat.find_min' hex hij.2
  · by_contra h
    have hle : Nat.find hex ≤ j - 1 := by omega
    have hd := (p.blockEnd_strictMono hm).monotone hle
    have hf := Nat.find_spec hex
    omega

theorem blockIndex_pos (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {i : ℕ} (hi : 1 ≤ i) :
    1 ≤ p.blockIndex i := by
  obtain ⟨j, hj, hij⟩ := p.exists_mem_block hm i hi
  rwa [p.blockIndex_eq_of_mem hm hij]

theorem flattenedCost_eq_of_mem (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {j n : ℕ} (hn : n + 1 ∈ p.block j) :
    p.flattenedCost n = p.C j := by
  simp only [flattenedCost, p.blockIndex_eq_of_mem hm hn]

end Invariant233.CircleParameterData

end OAI
