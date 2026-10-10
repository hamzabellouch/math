import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFolnerMean
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! # Counting measure converts metric Følner sets to invariant means -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric MeasureTheory Filter Set
open scoped Topology ENNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [DecidableEq G]

theorem coe_finiteMetricNeighborhood
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : Finset G) {R : ℝ} (hR : 0 ≤ R) :
    (↑(finiteMetricNeighborhood hfinite E R) : Set G) = cthickening R (E : Set G) := by
  rw [E.finite_toSet.isCompact.cthickening_eq_biUnion_closedBall hR]
  ext x
  simp only [Finset.mem_coe, mem_finiteMetricNeighborhood, Set.mem_iUnion, mem_closedBall,
    exists_prop]

variable [MeasurableSpace G] [BorelSpace G]

theorem invariantMean_of_countMetricFolner
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (A : ℕ → Set G) (hzero : ∀ n, Measure.count (A n) ≠ 0)
    (hfin : ∀ n, Measure.count (A n) ≠ ∞)
    (hratio : ∀ R : ℝ, 0 ≤ R →
      Tendsto (fun n => Measure.count (cthickening R (A n)) / Measure.count (A n))
        atTop (𝓝 1)) : Nonempty (InvariantMean G) := by
  have hA (n : ℕ) : (A n).Finite :=
    Measure.count_apply_lt_top.mp (lt_top_iff_ne_top.mpr (hfin n))
  let E := fun n => (hA n).toFinset
  have hEset (n : ℕ) : (↑(E n) : Set G) = A n := (hA n).coe_toFinset
  have hE (n : ℕ) : (E n).Nonempty := by
    apply Finset.coe_nonempty.mp
    rw [hEset]
    exact Measure.count_ne_zero_iff.mp (hzero n)
  apply invariantMean_of_metricBoundary_sequence hfinite E hE
  intro R hR
  let N := fun n => finiteMetricNeighborhood hfinite (E n) R
  have hNset (n : ℕ) : (↑(N n) : Set G) = cthickening R (A n) := by
    rw [← hEset n]
    exact coe_finiteMetricNeighborhood hfinite (E n) hR
  have hN (n : ℕ) : E n ⊆ N n := by
    intro p hp
    exact (mem_finiteMetricNeighborhood hfinite (E n) R p).mpr ⟨p, hp, by simpa using hR⟩
  have heq (n : ℕ) :
      (Measure.count (cthickening R (A n)) / Measure.count (A n)).toReal =
        ((N n).card : ℝ) / (E n).card := by
    rw [← hNset n, ← hEset n, Measure.count_apply_finset, Measure.count_apply_finset,
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have ht : Tendsto (fun n => ((N n).card : ℝ) / (E n).card) atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp (hratio R hR)
    simpa only [Function.comp_def, heq, ENNReal.toReal_one] using h
  have hdiff (n : ℕ) : ((N n \ E n).card : ℝ) / (E n).card =
      ((N n).card : ℝ) / (E n).card - 1 := by
    have hc : ((N n \ E n).card : ℝ) + (E n).card = (N n).card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (hN n)
    have hne : ((E n).card : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hE n).card_pos).ne'
    field_simp [hne]
    linarith
  simpa only [← hdiff, sub_self] using ht.sub_const 1

end PolycyclicRecognition

end

end OAI
