import OAI.Analysis.IrrationalRotation.Analysis.TailScaleCover
import OAI.Analysis.IrrationalRotation.Model.PhaseFailure

namespace OAI

noncomputable section
open Set

namespace Invariant233.ProductPhases

open TailScaleCover

theorem exists_tail_thresholds
    {ι : Type*} (J : ℕ → Finset ι) (K G κ L C : ℕ → ℝ) (θ : ι → ℝ)
    (j : ℕ)
    (hsize : ∀ s, j ≤ s → 100 ≤ (J s).card)
    (hgrowth : ∀ s, j ≤ s → 2 ^ s ≤ (J s).card)
    (hG : ∀ s, j ≤ s → 1 ≤ G s ∧ 4 * G s ≤ ((J s).card : ℝ))
    (hgap : ∀ s, j ≤ s → G (s + 1) * K (s + 1) < upperHorizon (J s).card)
    (hL : ∀ s, j ≤ s → L j ≤ L s)
    (hC : ∀ s, j ≤ s → L s ≤ C s)
    (hlargeIntensity : ∀ s, j ≤ s → L s ≤ κ s * ((J s).card : ℝ) ^ (1 / 40 : ℝ))
    (hsmallIntensity : ∀ s, j ≤ s → L s ≤ κ (s + 1) * Real.sqrt (G (s + 1)))
    (hsmall : ∀ s, j < s → smallPhaseCondition (J s) (K s) (G s) θ)
    (hlarge : ∀ s, j ≤ s → largePhaseCondition (J s) (((J s).card : ℝ) * K s) θ)
    (k : ℤ) (hk : ((J j).card : ℝ) * K j / 4 ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : ℝ) (I : Finset ι),
      j ≤ s ∧ (w = ((J s).card : ℝ) ^ (-(19 / 20 : ℝ)) ∨
        (j < s ∧ w = G s / (J s).card)) ∧
      w ∈ Set.Icc (1 / ((J s).card : ℝ)) (1 / 4) ∧
      I ⊆ J s ∧ ((J s).card : ℝ) / 20 ≤ I.card ∧
      (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w)) ∧
      L j ≤ ((J s).card : ℝ) * CouplingMarginalBounds.rho (κ s) (J s).card w ∧
      L j ≤ C s := by
  classical
  have hunbounded (R : ℝ) : ∃ s, j ≤ s ∧ R ≤ upperHorizon (J s).card := by
    obtain ⟨n, hn⟩ := exists_nat_gt R
    let s := max j n
    have hjs : j ≤ s := le_max_left _ _
    have hsm : s ≤ (J s).card := (Nat.lt_two_pow_self (n := s)).le.trans (hgrowth s hjs)
    refine ⟨s, hjs, ?_⟩
    calc
      R ≤ (n : ℝ) := hn.le
      _ ≤ (s : ℝ) := by exact_mod_cast le_max_right j n
      _ ≤ ((J s).card : ℝ) := by exact_mod_cast hsm
      _ ≤ upperHorizon (J s).card := self_le_upperHorizon (by
        have := hsize s hjs
        omega)
  obtain ⟨s, hjs, hs⟩ := exists_window (fun s => G s * K s)
    (fun s => ((J s).card : ℝ) * K s / 4) (fun s => upperHorizon (J s).card)
    j (fun s hs => (hgap s hs).le) hunbounded hk
  have hm100 : (100 : ℝ) ≤ (J s).card := by exact_mod_cast hsize s hjs
  have hm : (0 : ℝ) < (J s).card := by linarith
  have hwidths := widths_mem_Icc (by linarith : (16 : ℝ) ≤ (J s).card)
    (hG s hjs).1 (hG s hjs).2
  have hcost : L j ≤ C s := (hL s hjs).trans (hC s hjs)
  rcases hs with hhigh | hlow
  · let w : ℝ := ((J s).card : ℝ) ^ (-(19 / 20 : ℝ))
    have hcount : ((J s).card : ℝ) / 20 ≤
        (((J s).filter (fun i =>
          1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w))).card : ℝ) := by
      simpa only [phaseGoodCount, w, neg_div] using
        hlarge s hjs k hhigh.1 hhigh.2
    refine ⟨s, w, (J s).filter (fun i =>
        1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w)),
      hjs, Or.inl rfl, hwidths.2, Finset.filter_subset _ _,
      hcount, ?_, ?_, hcost⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · rw [show w = ((J s).card : ℝ) ^ (-(19 / 20 : ℝ)) from rfl,
        intensity_large _ _ hm]
      exact (hL s hjs).trans (hlargeIntensity s hjs)
  · refine ⟨s, G s / (J s).card, J s, hjs, Or.inr ⟨hlow.1, rfl⟩,
      hwidths.1, Finset.Subset.refl _, ?_,
      hsmall s hlow.1 k hlow.2.1 hlow.2.2, ?_, hcost⟩
    · linarith [hm.le]
    · rw [intensity_small _ _ _ hm (by linarith [(hG s hjs).1])]
      have hprev : j ≤ s - 1 := by omega
      have hi := hsmallIntensity (s - 1) hprev
      rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hi
      exact (hL (s - 1) hprev).trans hi

end Invariant233.ProductPhases

end

end OAI
