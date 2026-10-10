import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsBounded
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFamily
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourcePrimeSets

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries
open scoped BigOperators

lemma interior_cell_indices (I : Finset ℤ) (b e c : ℝ) (_hc : 0 < c)
    (hlarge : 4 ≤ c*b) (hcard : c*b ≤ I.card)
    (hband : ∀ h∈I,b ≤ (h:ℝ) ∧ (h:ℝ) ≤ e) :
    ∃ J : Finset ℤ,J ⊆ I ∧ (c/2)*b ≤ J.card ∧
      ∀ h∈J,b < (h:ℝ) ∧ (h:ℝ)+1 ≤ e := by
  classical
  let J := I \ {⌈b⌉,⌊e⌋}
  have hJ : J ⊆ I := Finset.sdiff_subset
  have hcount : I.card ≤ J.card+2 := by
    have ht : ({⌈b⌉,⌊e⌋}:Finset ℤ).card ≤ 2 := Finset.card_le_two
    exact Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add_left ht _)
  refine ⟨J,hJ,?_,?_⟩
  · have hh : (I.card:ℝ) ≤ (J.card:ℝ)+2 := by exact_mod_cast hcount
    nlinarith
  · intro h hh
    obtain ⟨hi,hne⟩ := Finset.mem_sdiff.mp hh
    have hne1 : h≠⌈b⌉ := by intro he; exact hne (by simp [he])
    have hne2 : h≠⌊e⌋ := by intro he; exact hne (by simp [he])
    have hl : ⌈b⌉ < h := lt_of_le_of_ne (Int.ceil_le.mpr (hband h hi).1) (Ne.symm hne1)
    have hu : h < ⌊e⌋ := lt_of_le_of_ne (Int.le_floor.mpr (hband h hi).2) hne2
    constructor
    · have hh' : (⌈b⌉:ℝ) < h := by exact_mod_cast hl
      exact (Int.le_ceil b).trans_lt hh'
    · exact Int.lt_floor_iff.mp hu

lemma boundedRawLogCell_interval_eq {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (a b : ℝ) (h : ℤ) (hlo : Real.exp a < (h:ℝ))
    (hhi : (h:ℝ)+1 ≤ Real.exp b) :
    boundedRawLogCell (boundedInterval E a b) h=boundedRawLogCell E h := by
  classical
  ext p
  simp only [boundedRawLogCell,boundedInterval,Finset.mem_filter]
  constructor
  · exact fun hh => ⟨hh.1.1,hh.2⟩
  · rintro ⟨hp,hl,hu⟩
    have hlog : 0 < Real.log p.val := Real.log_pos (by exact_mod_cast (primeUpTo_prime p).one_lt)
    have ha : a < Real.log (Real.log p.val) := by
      apply Real.exp_lt_exp.mp
      rw [Real.exp_log hlog]
      exact hlo.trans_le hl
    have hb : Real.log (Real.log p.val) ≤ b := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_log hlog]
      exact hu.le.trans hhi
    exact ⟨⟨hp,ha,hb⟩,hl,hu⟩

theorem exists_many_good_original_cells (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) :
    ∃ c a₀ : ℝ,0 < c ∧ ∀ (d : Decomposition) (Q : ℕ)
      (E : Finset (PrimeUpTo Q)) (F : HigherBiasSourceFamily d Q E δ)
      (a : ℝ) (n : ℤ),a₀ ≤ a →
      c₀ ≤ primeShellMass (boundedInterval E a (a+1)) →
      ∀ hm : 0 < primeShellMass (boundedInterval E a (a+1)),
      δ/2 ≤ ((primeShellPrior (boundedInterval E a (a+1)) hm).cmean
        (fun p=>F.test p (n:ZMod p.val))).re →
      ∃ I : Finset ℤ,c*Real.exp a ≤ I.card ∧ ∀ h∈I,
        Real.exp a < (h:ℝ) ∧ (h:ℝ)+1 ≤ Real.exp (a+1) ∧
        c/Real.exp a ≤ primeShellMass (boundedRawLogCell E h) ∧
        ∃ hmass : 0 < primeShellMass (boundedRawLogCell E h),
          δ/4 ≤ ((primeShellPrior (boundedRawLogCell E h) hmass).cmean
            (fun p=>F.test p (n:ZMod p.val))).re := by
  classical
  obtain ⟨c,b₀,hc,hb₀,hcells⟩ := exists_many_good_bounded_prime_cells c₀ δ hc₀ hδ
  refine ⟨c/2,Real.log (max b₀ (4/c)),by positivity,?_⟩
  intro d Q E F a n ha hmass hm hmean
  have hbpos : 0 < max b₀ (4/c) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hlarge : max b₀ (4/c) ≤ Real.exp a := by
    simpa only [Real.exp_log hbpos] using Real.exp_le_exp.mpr ha
  have hb : b₀ ≤ Real.exp a := (le_max_left _ _).trans hlarge
  have h4 : 4 ≤ c*Real.exp a := by
    have hh := (le_max_right b₀ (4/c)).trans hlarge
    exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  obtain ⟨I,hI,hgood⟩ := hcells Q (boundedInterval E a (a+1))
    (fun p=>F.test p (n:ZMod p.val)) (Real.exp a) hb
    (by
      intro p hp
      have hh := boundedInterval_log_bounds E a (a+1) p hp
      exact ⟨hh.1.le,by simpa only [Real.exp_add,mul_comm] using hh.2⟩)
    hmass (fun p _=>F.test_norm_le_one p _) (by
      rw [prior_cmean_re,primeShellPrior_real_mean] at hmean
      exact hmean)
  obtain ⟨J,hJI,hJ,hint⟩ := interior_cell_indices I (Real.exp a) (Real.exp (a+1)) c hc h4 hI
    (by
      intro h hh
      have he : Real.exp (a+1)=Real.exp 1*Real.exp a := by rw [Real.exp_add]; ring
      exact ⟨(hgood h hh).1,he ▸ (hgood h hh).2.1⟩)
  refine ⟨J,hJ,?_⟩
  intro h hh
  have heq := boundedRawLogCell_interval_eq E a (a+1) h (hint h hh).1 (hint h hh).2
  have hcm := (hgood h (hJI hh)).2.2.1
  have hct := (hgood h (hJI hh)).2.2.2
  rw [heq] at hcm hct
  have hcp : 0 < primeShellMass (boundedRawLogCell E h) := (div_pos hc (Real.exp_pos a)).trans_le hcm
  refine ⟨(hint h hh).1,(hint h hh).2,?_,hcp,?_⟩
  · exact (div_le_div_of_nonneg_right (by linarith : c/2 ≤ c) (Real.exp_pos a).le).trans hcm
  · rw [prior_cmean_re,primeShellPrior_real_mean]
    exact hct

end Ostmann.Characters.HigherBiasSource

end

end OAI
