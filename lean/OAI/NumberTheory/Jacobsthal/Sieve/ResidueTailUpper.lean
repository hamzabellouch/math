import OAI.NumberTheory.Jacobsthal.Sieve.ResidueCountDifference

namespace OAI

namespace Erdos970

section

namespace ErdosInverseTail
open NumberTheoryLean

theorem progressionSurvivors_mono (N M z : ℕ) (hNM : N ≤ M) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    ProgressionSmallSieve.progressionSurvivors N z b step a ⊆
      ProgressionSmallSieve.progressionSurvivors M z b step a := by
  intro j hj
  obtain ⟨hj,ha⟩ := SievePartition.mem_survivors.mp hj
  exact SievePartition.mem_survivors.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hNM),ha⟩

theorem sieve_tail_upper (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∃ w0 : ℝ,2 ≤ w0 ∧
      ∀ (J N : ℕ) (w L : ℝ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ),
        w0 ≤ w → w^eta ≤ L → ((N-J : ℕ) : ℝ) ≤ L →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → step.Coprime t) →
        ((sieveTail J N ⌊w⌋₊ b step a).card : ℝ) ≤ C*L*SmallSieveFinite.smallEuler ⌊w⌋₊ := by
  obtain ⟨C,hC,w0,hw0,hupper⟩ := SmallSieveUpper.progression_small_upper eta heta
  refine ⟨C,hC,w0,hw0,?_⟩
  intro J N w L b step a hw hL hNL hcop
  have hwpos : 0 < w := by linarith
  have hLpos : 0 < L := (Real.rpow_pos_of_pos hwpos eta).trans_le hL
  have hle : N-J ≤ ⌈L⌉₊ := by exact_mod_cast hNL.trans (Nat.le_ceil L)
  have hround : |(⌈L⌉₊ : ℝ)-L| ≤ 1 := by
    have hlo := Nat.le_ceil L
    have hhi := Nat.ceil_lt_add_one hLpos.le
    rw [abs_le]
    constructor <;> linarith
  rw [sieveTail_card]
  calc
    _ ≤ ((ProgressionSmallSieve.progressionSurvivors ⌈L⌉₊ ⌊w⌋₊ (b+(step : ℤ)*J) step a).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (progressionSurvivors_mono (N-J) ⌈L⌉₊ ⌊w⌋₊ hle _ step a)
    _ ≤ _ := hupper ⌈L⌉₊ w L (b+(step : ℤ)*J) step a hw hL hround hcop

theorem survivor_count_difference (J N z : ℕ) (hJN : J ≤ N) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    |((ProgressionSmallSieve.progressionSurvivors N z b step a).card : ℝ)-
      ((ProgressionSmallSieve.progressionSurvivors J z b step a).card : ℝ)| =
      (sieveTail J N z b step a).card := by
  rw [survivor_card_split J N z hJN b step a,Nat.cast_add,add_sub_cancel_left,
    abs_of_nonneg (Nat.cast_nonneg _)]

end ErdosInverseTail

end

section

namespace ErdosInverseTail
open NumberTheoryLean ErdosInverseHits

theorem residue_tail_upper (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∃ w0 : ℝ,2 ≤ w0 ∧
      ∀ (J N u : ℕ) [NeZero u] (e : ZMod u) (w L : ℝ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ),
        w0 ≤ w → w^eta ≤ L/(u : ℝ) → ((N-J : ℕ) : ℝ) ≤ L →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (step*u).Coprime t) →
        (((sieveTail J N ⌊w⌋₊ b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card : ℝ) ≤
          2*C*(L/(u : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊ := by
  obtain ⟨C,hC,w0,hw0,hupper⟩ := SmallSieveUpper.progression_small_upper eta heta
  refine ⟨C,hC,w0,hw0,?_⟩
  intro J N u inst e w L b step a hw hL hNL hcop
  have hu : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hw1 : 1 ≤ w := by linarith
  have hratio1 : 1 ≤ L/(u : ℝ) := (Real.one_le_rpow hw1 heta.le).trans hL
  have hlong : w^eta ≤ 2*(L/(u : ℝ)) := hL.trans (by linarith)
  have hlongpos : 0 < 2*(L/(u : ℝ)) := by linarith
  have hr := residueOffset_lt J u e
  have herr := hitLength_error (N-J) u (residueOffset J u e+1) hu (by omega) (by omega)
  have hT : (hitLength (N-J) u (residueOffset J u e+1) : ℝ) ≤ 2*(L/(u : ℝ)) := by
    have hh := (abs_le.mp herr).2
    have hdiv := div_le_div_of_nonneg_right hNL huR.le
    linarith
  have hle : hitLength (N-J) u (residueOffset J u e+1) ≤ ⌈2*(L/(u : ℝ))⌉₊ := by
    exact_mod_cast hT.trans (Nat.le_ceil (2*(L/(u : ℝ))))
  have hround : |(⌈2*(L/(u : ℝ))⌉₊ : ℝ)-2*(L/(u : ℝ))| ≤ 1 := by
    have hlo := Nat.le_ceil (2*(L/(u : ℝ)))
    have hhi := Nat.ceil_lt_add_one hlongpos.le
    rw [abs_le]
    constructor <;> linarith
  rw [residue_tail_card]
  calc
    _ ≤ ((ProgressionSmallSieve.progressionSurvivors ⌈2*(L/(u : ℝ))⌉₊ ⌊w⌋₊
        (b+(step : ℤ)*((J+residueOffset J u e : ℕ) : ℤ)) (step*u) a).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (progressionSurvivors_mono _ _ ⌊w⌋₊ hle _ (step*u) a)
    _ ≤ C*(2*(L/(u : ℝ)))*SmallSieveFinite.smallEuler ⌊w⌋₊ :=
      hupper _ w _ _ (step*u) a hw hlong hround hcop
    _ = _ := by ring

end ErdosInverseTail

end

end Erdos970

end OAI
