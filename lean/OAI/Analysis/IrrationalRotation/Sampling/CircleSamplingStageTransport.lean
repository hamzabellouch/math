import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingBlocks
import OAI.Analysis.IrrationalRotation.Sampling.PhaseRanges
import OAI.Analysis.IrrationalRotation.Model.CircleSamplingStage

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.CircleParameterData

theorem samplingAverage_eq_trialAverage (p : CircleParameterData)
    (θ : ℝ) (j r : ℕ) (hj : 1 ≤ j) (endpoint : Bool) (x : Circle) :
    p.samplingAverage θ j r endpoint x =
      TrialSampling.average (p.m j) (p.samples j r) endpoint
        (fun i : Fin (p.m j) => p.alpha θ (p.blockEnd (j - 1) + i.val + 1))
        (fun i : Fin (p.m j) =>
          (p.q (p.blockEnd (j - 1) + i.val + 1) : ℤ) • x) := by
  rw [p.samplingAverage_eq_characterAverage θ j r hj endpoint x,
    CharacterSampling.average_eq_trialAverage]

theorem card_filter_block_eq_fin (p : CircleParameterData) (j : ℕ)
    (hj : 1 ≤ j) (P : ℕ → Prop) [DecidablePred P] :
    ((p.block j).filter P).card =
      ((Finset.univ : Finset (Fin (p.m j))).filter
        (fun i => P (p.blockEnd (j - 1) + i.val + 1))).card := by
  classical
  have hend : p.blockEnd j = p.blockEnd (j - 1) + p.m j := by
    simpa only [Nat.sub_add_cancel hj] using p.blockEnd_succ (j - 1)
  symm
  apply Finset.card_bij (fun i _ => p.blockEnd (j - 1) + i.val + 1)
  · intro i hi
    refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hi).2⟩
    rw [mem_block_iff, hend]
    have h := i.isLt
    omega
  · intro i hi k hk heq
    apply Fin.ext
    omega
  · intro i hi
    obtain ⟨hib, hiP⟩ := Finset.mem_filter.mp hi
    obtain ⟨hlo, hhi⟩ := (p.mem_block_iff j i).mp hib
    rw [hend] at hhi
    let t : Fin (p.m j) := ⟨i - p.blockEnd (j - 1) - 1, by omega⟩
    have ht : p.blockEnd (j - 1) + t.val + 1 = i := by
      dsimp [t]
      omega
    refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ht⟩
    simpa only [ht] using hiP

theorem spread_high_of_strict_fin (p : CircleParameterData) (θ : ℝ)
    (j : ℕ) (hj : 1 ≤ j)
    (h : ProductPhases.strictLargePhaseCondition Finset.univ (p.N j)
      (fun i : Fin (p.m j) => p.alpha θ (p.blockEnd (j - 1) + i.val + 1))) :
    ∀ k : ℤ, p.N j / 4 ≤ |(k : ℝ)| →
      |(k : ℝ)| ≤ (p.m j : ℝ) ^ ((4 / 5 : ℝ) * p.m j) →
      (p.m j : ℝ) / 20 ≤
        ((p.block j).filter (fun i =>
          1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Icc (p.b j) (1 - p.b j))).card := by
  classical
  intro k hlo hhi
  have hs := h k hlo (by simpa only [Finset.card_univ, Fintype.card_fin] using hhi)
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  rw [p.card_filter_block_eq_fin j hj]
  apply hs.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiU, hiP⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨hiU, ?_⟩
  simpa only [b, neg_div] using (show
    1 - Int.fract ((k : ℝ) * p.alpha θ (p.blockEnd (j - 1) + i.val + 1)) ∈
      Icc ((p.m j : ℝ) ^ (-19 / 20 : ℝ))
        (1 - (p.m j : ℝ) ^ (-19 / 20 : ℝ)) from ⟨hiP.1.le, hiP.2.le⟩)

theorem spread_low_of_phase_bounds (p : CircleParameterData) (θ : ℝ)
    (j : ℕ) (hm : 0 < p.m j) (hK : 0 < p.K j) (hG : 0 < p.G j)
    (hphase : ∀ i ∈ p.block j,
      1 / p.N j < p.alpha θ i ∧ p.alpha θ i < 2 / p.N j) :
    ∀ k : ℤ, (p.G j : ℝ) * p.K j ≤ |(k : ℝ)| →
      |(k : ℝ)| ≤ p.N j / 4 → ∀ i ∈ p.block j,
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Icc (p.a j) (1 - p.a j) := by
  intro k hlo hhi i hi
  exact phase_small_window (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hK)
    (Nat.cast_pos.mpr hG) (hphase i hi).1.le (hphase i hi).2.le hlo hhi

end Invariant233.CircleParameterData

end

end OAI
