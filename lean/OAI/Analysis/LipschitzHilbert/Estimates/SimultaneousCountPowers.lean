import OAI.Analysis.LipschitzHilbert.Estimates.SimultaneousCount
import OAI.Analysis.LipschitzHilbert.Estimates.CountGeometryParameters

namespace OAI

/-! The simultaneous count at the manuscript's polynomial thresholds. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

/-- The finite-family version of §6's simultaneous-count proposition:
an `S exp(-J L)` exceptional set and the uniform `D/100` list bound.
The small-time hypothesis is stated in the precise strength used by
the proved Lipschitz transfer, and all numerical choices are explicit. -/
theorem simultaneous_separated_count_powers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → SlopeBox) (u : ℝ × ℝ → ℝ) {Lip : ℝ≥0} (hu : LipschitzWith Lip u)
    {L a k p t c c0 B m J : ℝ} {M : ℕ}
    (hL : 15 ≤ L) (ha : 0 ≤ a)
    (hap : a + 1 ≤ p) (hkp : k + 1 ≤ p) (ht : 2 * a + p + 1 ≤ t)
    (hlarge : 240 * (1 + c) * (|Real.log 768| + |2 * p| + J) ≤ L)
    (hM : 0 < M) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    (hcM : c ≤ M) (hB : 1 < B) (hMB : (M : ℝ) = B ^ 2) (hm : B ^ 2 ≤ m)
    (d : ι → ℝ) (E : ι → Set (ℝ × ℝ))
    (hE : ∀ i, MeasurableSet (E i))
    (hfinite : ∀ i, (volume.prod volume) (E i) ≠ ∞)
    (hbox : ∀ i, ∀ w ∈ E i, (T i).radius w ≤ L ^ a)
    (harea : ∀ i, L ^ (-a) * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hwitness : ∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i)
    (hd : ∀ i, 0 ≤ d i) (hwidth : ∀ i, (T i).width = m * (T i).length * d i)
    (hsmall : ∀ i, Lip * L ^ p * m * (T i).length ≤ 1 / 2) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
      (volume.prod volume).real bad ≤
        (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) ∧
      ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
        (∀ i ∈ I, (T i).radius z ≤ L ^ k) →
        (∀ i ∈ I, d i ≤ rho / B ^ 2) →
        (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho) →
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
        (I.card : ℝ) ≤ L ^ (t + 4) / 100 := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hc' : 0 ≤ c := by linarith
  obtain ⟨bad, hmeas, hfiniteBad, hmeasure, hcount⟩ := simultaneous_separated_count T u hu hM
    (Real.rpow_pos_of_pos hL0 a) (Real.rpow_pos_of_pos hL0 (-a))
    (Real.rpow_pos_of_pos hL0 p) (Real.rpow_nonneg hL0.le k)
    (count_witness_dilation (by linarith) hap hkp) hc0 hc hcM hB hMB hm
    (Real.rpow_pos_of_pos hL0 (-t)) (count_popular_threshold (by linarith) ht)
    (Real.rpow_nonneg hL0.le (t + 2)) d E hE hfinite hbox harea hwitness hd hwidth hsmall
  refine ⟨bad, hmeas, hfiniteBad, ?_, ?_⟩
  · have hbudget := count_power_budget (a := t) hL1 (by linarith : k ≤ p) hc' hlarge
    have hbudget' : 384 * L ^ k * (L ^ k + L ^ p) *
        Real.exp (-(L ^ (-t)) * L ^ (t + 2) / (240 * (1 + c))) ≤ Real.exp (-J * L) := by
      simpa only [neg_mul] using hbudget
    exact hmeasure.trans (mul_le_mul_of_nonneg_left hbudget'
      (Finset.sum_nonneg fun i _ => mul_nonneg (T i).length_pos.le (T i).width_pos.le))
  · intro z hz rho hrho I hsignificant hprecision hspan hsep
    exact (hcount z hz rho hrho I hsignificant hprecision hspan hsep).trans
      (count_direction_margin hL (by linarith : 0 ≤ t))

end LipschitzHilbert

end

end OAI
