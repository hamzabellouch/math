import OAI.NumberTheory.JointDickman.Analysis.MellinBandSelection

namespace OAI

/-! # Ordinary dyadic density of the selected canonical cutoff -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem selected_dyadic_missing : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ P Q η : ℝ, 2 ≤ P → P ≤ Q →
      ∀ hQ : 1 ≤ Real.log Q,
      (((Ioc N (2*N)).filter fun n =>
        ¬mrtTypical (range (mellinBandCount Q (Real.sqrt (Real.log (N:ℝ))) hQ))
          (canonicalMellinBands P Q η).primes n).card:ℝ)/N ≤ C*Real.log P/Real.log Q := by
  obtain ⟨C,hC,hbound⟩ := selected_mellin_count
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound.filter_mono tendsto_natCast_atTop_atTop] with N hN
  intro P Q η hP hPQ hQ
  apply le_trans _ (hN P Q η hP hPQ hQ)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hn,hbad⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨mem_range.mpr ?_,hbad⟩
  have hle : (n:ℝ) ≤ 3*(N:ℝ) := by
    have hh : (n:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast (mem_Ioc.mp hn).2
    linarith [show (0:ℝ)≤N by positivity]
  have hlt : (n:ℝ) < (⌊3*(N:ℝ)⌋₊:ℝ)+1 :=
    hle.trans_lt (Nat.lt_floor_add_one (3*(N:ℝ)))
  exact_mod_cast hlt

end JointDickman

end OAI
