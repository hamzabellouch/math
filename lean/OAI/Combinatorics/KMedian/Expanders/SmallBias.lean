import Mathlib
import OAI.Combinatorics.KMedian.Expanders.Cayley
import OAI.Combinatorics.KMedian.Expanders.Rademacher

namespace OAI

section Inline_PCPSmallBias

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

lemma testRate_exists_le_sum {S B : Type} [Fintype S] [Fintype B] (p : B → S → Prop) :
    testRate (fun s => ∃ b, p b s) ≤ ∑ b, testRate (p b) := by
  classical
  unfold testRate
  rw [← expect_sum_comm]
  apply expect_le_expect
  intro s _
  by_cases h : ∃ b, p b s
  · rw [ite_eq_left h]
    obtain ⟨b,hb⟩ := h
    calc
      (1:ℝ) = (if p b s then 1 else 0) := by rw [ite_eq_left hb]
      _ ≤ ∑ b, if p b s then (1:ℝ) else 0 :=
        single_le_sum (f := fun b => if p b s then (1:ℝ) else 0)
          (fun b _ => by split_ifs <;> norm_num) (mem_univ b)
  · rw [ite_eq_right h]
    exact sum_nonneg (fun b _ => by split_ifs <;> norm_num)

namespace Walsh
variable {I : Type} [Fintype I] [DecidableEq I]

lemma small_bias_word_bound (b : BitVector I) (n : ℕ) (ρ : ℝ) (hn : 0 < n) (hρ : 0 < ρ) :
    testRate (fun g : Fin n → BitVector I => b≠0 ∧ ρ ≤ |bias g b|) * ((n:ℝ)*ρ)^10 ≤
      945*(n:ℝ)^5 := by
  classical
  by_cases hb : b=0
  · subst b
    have he : testRate (fun g : Fin n → BitVector I => (0:BitVector I)≠0 ∧ ρ ≤ |bias g 0|)=0 := by
      simp [testRate]
    rw [he,zero_mul]
    positivity
  have hbmean : (𝔼 x, character b x)=0 := by rw [character_mean,ite_eq_right hb]
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hh := Rademacher.large_sum_rate (character b) (character_cases b) hbmean n ((n:ℝ)*ρ)
    (mul_pos hnR hρ)
  have hi : testRate (fun g : Fin n → BitVector I => b≠0 ∧ ρ ≤ |bias g b|) ≤
      testRate (fun g : Fin n → BitVector I => (n:ℝ)*ρ ≤ |Rademacher.wordSum (character b) n g|) := by
    apply testRate_mono
    intro g hg
    unfold bias at hg
    rw [Fintype.expect_eq_sum_div_card] at hg
    simp only [Fintype.card_fin,abs_div,abs_of_pos hnR] at hg
    change (n:ℝ)*ρ ≤ |∑ i, character b (g i)|
    have ht := (le_div_iff₀ hnR).mp hg.2
    simpa only [mul_comm] using ht
  exact (mul_le_mul_of_nonneg_right hi (by positivity)).trans hh

theorem exists_small_bias (n : ℕ) (ρ : ℝ) (hn : 0 < n) (hρ : 0 < ρ)
    (hsize : (Fintype.card (BitVector I):ℝ)*945*(n:ℝ)^5 < ((n:ℝ)*ρ)^10) :
    ∃ g : Fin n → BitVector I, ∀ b, b≠0 → |bias g b| < ρ := by
  classical
  let p (b : BitVector I) (g : Fin n → BitVector I) := b≠0 ∧ ρ ≤ |bias g b|
  have hu := testRate_exists_le_sum p
  have hbound : testRate (fun g : Fin n → BitVector I => ∃ b, p b g) * ((n:ℝ)*ρ)^10 ≤
      (Fintype.card (BitVector I):ℝ)*945*(n:ℝ)^5 := by
    calc
      _ ≤ (∑ b, testRate (p b))*((n:ℝ)*ρ)^10 := mul_le_mul_of_nonneg_right hu (by positivity)
      _ = ∑ b, testRate (p b)*((n:ℝ)*ρ)^10 := sum_mul _ _ _
      _ ≤ ∑ _b : BitVector I, 945*(n:ℝ)^5 := sum_le_sum (fun b _ => small_bias_word_bound b n ρ hn hρ)
      _ = _ := by simp; ring
  have hlt : testRate (fun g : Fin n → BitVector I => ∃ b, p b g) < 1 := by
    have hh := hbound.trans_lt hsize
    have hw : 0 < ((n:ℝ)*ρ)^10 := pow_pos (mul_pos (Nat.cast_pos.mpr hn) hρ) _
    nlinarith
  by_contra h
  push Not at h
  have hall : ∀ g : Fin n → BitVector I, ∃ b, p b g := by
    intro g
    obtain ⟨b,hb,hbad⟩ := h g
    exact ⟨b,hb,hbad⟩
  have he : testRate (fun g : Fin n → BitVector I => ∃ b, p b g)=1 := by
    rw [testRate_congr (fun g => iff_true_intro (hall g)),testRate_true]
  linarith

theorem exists_base_generators : ∃ g : Fin (2^44) → BitVector (Fin 176),
    ∀ b, b≠0 → |bias g b| ≤ 1/10 := by
  obtain ⟨g,hg⟩ := exists_small_bias (I := Fin 176) (2^44) (1/10) (by positivity) (by norm_num)
    (by simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card]; norm_num)
  exact ⟨g,fun b hb => le_of_lt (hg b hb)⟩

noncomputable def baseGenerators : Fin (2^44) → BitVector (Fin 176) :=
  Classical.choose exists_base_generators
noncomputable def baseGraph : PortGraph (BitVector (Fin 176)) (Fin (2^44)) := cayley baseGenerators

theorem baseGraph_contracts : baseGraph.Contracts (1/10) :=
  cayley_contracts baseGenerators (1/10) (Classical.choose_spec exists_base_generators)

end Walsh
end MetricKMedian.PCP

end Inline_PCPSmallBias

end OAI
