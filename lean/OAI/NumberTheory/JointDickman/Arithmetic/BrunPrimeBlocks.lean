import OAI.NumberTheory.JointDickman.Arithmetic.BrunBlocks
import OAI.NumberTheory.JointDickman.Arithmetic.SieveDimensionLog

namespace OAI

/-! # Dyadic logarithmic prime blocks -/
namespace JointDickman
open Finset

noncomputable def brunPrimeBlock (P : Finset ℕ) (L : ℝ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p => L/(2:ℝ)^(j+1) < Real.log p ∧ Real.log p ≤ L/(2:ℝ)^j)

 theorem brunPrimeBlock_subset (P : Finset ℕ) (L : ℝ) (j : ℕ) : brunPrimeBlock P L j ⊆ P :=
  filter_subset _ _

 theorem brun_level_antitone {L : ℝ} (hL : 0 ≤ L) {i j : ℕ} (hij : i ≤ j) :
    L/(2:ℝ)^j ≤ L/(2:ℝ)^i := by
  exact div_le_div_of_nonneg_left hL (by positivity)
    (pow_le_pow_right₀ (by norm_num) hij)

 theorem brunPrimeBlock_disjoint (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Pairwise (fun i j : ℕ => Disjoint (brunPrimeBlock P L i) (brunPrimeBlock P L j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := (mem_filter.mp hpi).2
  have hj := (mem_filter.mp hpj).2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (not_lt_of_ge (hj.2.trans (brun_level_antitone hL hlt))) hi.1
  · exact (not_lt_of_ge (hi.2.trans (brun_level_antitone hL hgt))) hj.1

 theorem brunPrimeBlocks_disjoint (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    Pairwise (fun i j : Fin N => Disjoint (brunPrimeBlock P L i.val) (brunPrimeBlock P L j.val)) := by
  intro i j hij
  exact brunPrimeBlock_disjoint P hL (fun h => hij (Fin.ext h))

 theorem brunPrimeBlocks_union (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) (N : ℕ)
    (hN : ∀ p ∈ P, L/(2:ℝ)^N < Real.log p) :
    brunBlockUnion (fun j : Fin N => brunPrimeBlock P L j.val) =
      P.filter (fun p : ℕ => Real.log p ≤ L) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
    obtain ⟨hp,hlo,hhi⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hp,hhi.trans (by simpa using brun_level_antitone hL (Nat.zero_le i.val))⟩
  · intro hp
    obtain ⟨hp,hpL⟩ := mem_filter.mp hp
    have hex : ∃ n : ℕ, L/(2:ℝ)^n < Real.log p := ⟨N,hN p hp⟩
    let n := Nat.find hex
    have hn : L/(2:ℝ)^n < Real.log p := Nat.find_spec hex
    have hnN : n ≤ N := Nat.find_min' hex (hN p hp)
    have hn0 : n ≠ 0 := by
      intro he
      simp only [he,pow_zero,div_one] at hn
      exact (not_lt_of_ge hpL) hn
    have hj : n-1 < N := by omega
    have hjp : Real.log p ≤ L/(2:ℝ)^(n-1) := by
      exact le_of_not_gt (Nat.find_min hex (show n-1 < n by omega))
    apply mem_biUnion.mpr
    refine ⟨⟨n-1,hj⟩,mem_univ _,mem_filter.mpr ⟨hp,?_,hjp⟩⟩
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)] using hn

 theorem exists_brun_block_depth (L : ℝ) : ∃ N : ℕ, L/(2:ℝ)^N < Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (L/Real.log 2) (by norm_num : (1:ℝ)<2)
  refine ⟨N,(div_lt_iff₀ (by positivity)).mpr ?_⟩
  exact (div_lt_iff₀ hlog).mp hN |>.trans_eq (mul_comm _ _)

end JointDickman

end OAI
