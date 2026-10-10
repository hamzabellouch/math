import OAI.MeasureTheory.Falconer.Recursion.DyadicWindowInterpolation
import OAI.MeasureTheory.Falconer.Estimates.Availability

namespace OAI

/-! # Turning the improved scale window into the manuscript's radial cap bound -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem exists_radial_window_denominator {e q : ℝ} (he : 0 < e) (hq : 0 ≤ q) :
    ∃ K : ℕ, 0 < K ∧ ∀ N : ℕ, ((N/K:ℕ):ℝ)*q ≤ (N:ℝ)*e := by
  obtain ⟨K,hK⟩ := exists_nat_gt (q/e)
  have hKe : q < (K:ℝ)*e := (div_lt_iff₀ he).mp hK
  have hKpos : 0 < K := by
    have hh : (0:ℝ) < K := lt_of_le_of_lt (div_nonneg hq he.le) hK
    exact_mod_cast hh
  refine ⟨K,hKpos,fun N => ?_⟩
  have hKr : (0:ℝ) < K := by exact_mod_cast hKpos
  calc
    _ ≤ ((N:ℝ)/(K:ℝ))*q := mul_le_mul_of_nonneg_right Nat.cast_div_le hq
    _ ≤ ((N:ℝ)/(K:ℝ))*((K:ℝ)*e) := mul_le_mul_of_nonneg_left hKe.le (by positivity)
    _ = _ := by field_simp

theorem radialCapBound_of_window {d N m : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (G : Set (Space d × Space d))
    (hmN : m ≤ N) {e q v : ℝ} (hq : 0 ≤ q) (hqv : q ≤ v)
    (hcoarse : (m:ℝ)*q ≤ (N:ℝ)*e)
    (hconstant : (2:ℝ)^v ≤ ((2:ℝ)^N)^e)
    (hdyadic : ∀ j : ℕ, m ≤ j → j ≤ N →
      (∀ x u : Space d, (μ : Measure (Space d))
        {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^j)^v)) ∧
      (∀ z u : Space d, (ν : Measure (Space d))
        {x | (z,x) ∈ G ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^j)^v))) : RadialCapBound μ ν G N e q := by
  have hμ (x w : Space d) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      (μ : Measure (Space d)) {z | (z,x) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤
        ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
    apply dyadic_window_interpolation
      (fun r => (μ : Measure (Space d)) {z | (z,x) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r})
      (fun _ _ hrs => measure_mono (fun _ hz => ⟨hz.1,hz.2.trans hrs⟩))
      (fun r => (measure_mono (subset_univ _)).trans_eq (measure_univ)) hmN hq hqv hcoarse hconstant
      (fun j hj hjN => (hdyadic j hj hjN).1 x w) hr hr1
  have hν (z w : Space d) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      (ν : Measure (Space d)) {x | (z,x) ∈ G ∧ ‖normalize (x-z)-w‖ ≤ r} ≤
        ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
    apply dyadic_window_interpolation
      (fun r => (ν : Measure (Space d)) {x | (z,x) ∈ G ∧ ‖normalize (x-z)-w‖ ≤ r})
      (fun _ _ hrs => measure_mono (fun _ hz => ⟨hz.1,hz.2.trans hrs⟩))
      (fun r => (measure_mono (subset_univ _)).trans_eq (measure_univ)) hmN hq hqv hcoarse hconstant
      (fun j hj hjN => (hdyadic j hj hjN).2 z w) hr hr1
  constructor
  · intro x _ w _ r hr hr1
    change (ν : Measure (Space d)) {y | (x,y) ∈ G ∧ ‖normalize (y-x)-w‖ < r} ≤ _
    apply le_trans _ (hν x w (by simpa only [one_div] using hr) hr1)
    exact measure_mono (fun _ hz => ⟨hz.1,hz.2.le⟩)
  · intro y _ w _ r hr hr1
    change (μ : Measure (Space d)) {x | (x,y) ∈ G ∧ ‖normalize (x-y)-w‖ < r} ≤ _
    apply le_trans _ (hμ y w (by simpa only [one_div] using hr) hr1)
    exact measure_mono (fun _ hz => ⟨hz.1,hz.2.le⟩)

end Falconer

end OAI
