import OAI.MeasureTheory.Falconer.Recursion.CriticalTruncatedPotential
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace OAI

/-! The critical dyadic potential of a finite scalar statistic, with one
explicit contribution per scale. This is used for the average projected
energy of a planar point set. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def scalarCountingMeasure (I : Finset ℝ) : Measure ℝ :=
  ∑ c ∈ I, Measure.dirac c

theorem scalarCountingMeasure_apply (I : Finset ℝ) (A : Set ℝ) :
    scalarCountingMeasure I A = (I.filter (fun c => c ∈ A)).card := by
  rw [scalarCountingMeasure,Measure.finsetSum_apply]
  simp_rw [Measure.dirac_apply,Set.indicator_apply,Pi.one_apply]
  rw [← Finset.sum_filter]
  simp

theorem scalarCountingMeasure_lintegral (I : Finset ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ c, f c ∂scalarCountingMeasure I) = ∑ c ∈ I, f c := by
  rw [scalarCountingMeasure,lintegral_finsetSum_measure]
  simp only [lintegral_dirac]

theorem finite_critical_statistic (I : Finset ℝ) (a : ℝ → ℝ)
    (ha : Measurable a) (ha0 : ∀ c, 0 ≤ a c) (N : ℕ) {s C : ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hsmall : ∀ j : ℕ, j ≤ N →
      ((I.filter fun c => a c < 1/(2:ℝ)^j).card:ℝ) ≤ C*(1/(2:ℝ)^j)^s) :
    (∑ c ∈ I, (1/max (a c) (1/(2:ℝ)^N))^s) ≤
      (I.card:ℝ)+(2:ℝ)^s*(C+(N:ℝ)*(C*(2:ℝ)^s)) := by
  let μ := scalarCountingMeasure I
  let A := {c : ℝ | a c < 1}
  let F := fun c => ENNReal.ofReal ((1/max (a c) (1/(2:ℝ)^N))^s)
  have hcounts (j : ℕ) (hj : j ≤ 0+N) :
      μ {c | a c < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (C*(1/(2:ℝ)^j)^s) := by
    rw [scalarCountingMeasure_apply]
    have hh := ENNReal.ofReal_le_ofReal (hsmall j (by simpa using hj))
    simpa only [ENNReal.ofReal_natCast,Set.mem_ofPred_eq] using hh
  have hnear := truncated_scalar_potential_critical μ a ha ha0 hs 0 N hcounts
  simp only [pow_zero,one_div_one,zero_add] at hnear
  have hfar : (∫⁻ c in Aᶜ, F c ∂μ) ≤ (I.card:ℝ≥0∞) := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1:ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' (by dsimp [A]; measurability)
        intro c hc
        have hc1 : 1 ≤ a c := le_of_not_gt hc
        have hd : 1 ≤ max (a c) (1/(2:ℝ)^N) := hc1.trans (le_max_left _ _)
        have hi : 1/max (a c) (1/(2:ℝ)^N) ≤ 1 :=
          (div_le_one (zero_lt_one.trans_le hd)).2 hd
        exact ENNReal.ofReal_le_one.mpr
          ((Real.rpow_le_rpow (by positivity) hi hs).trans_eq (Real.one_rpow s))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = I.card := by rw [scalarCountingMeasure_apply]; simp
  have htotal : (∑ c ∈ I, F c) ≤ (I.card:ℝ≥0∞)+
      ENNReal.ofReal ((2:ℝ)^s)*(ENNReal.ofReal C+(N:ℝ≥0∞)*ENNReal.ofReal (C*(2:ℝ)^s)) := by
    rw [← scalarCountingMeasure_lintegral]
    change (∫⁻ c, F c ∂μ) ≤ _
    rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
    exact (add_le_add hnear hfar).trans_eq (add_comm _ _)
  change (∑ c ∈ I, ENNReal.ofReal ((1/max (a c) (1/(2:ℝ)^N))^s)) ≤ _ at htotal
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)] at htotal
  have he : ENNReal.ofReal ((I.card:ℝ)+(2:ℝ)^s*(C+(N:ℝ)*(C*(2:ℝ)^s))) =
      (I.card:ℝ≥0∞)+ENNReal.ofReal ((2:ℝ)^s)*
        (ENNReal.ofReal C+(N:ℝ≥0∞)*ENNReal.ofReal (C*(2:ℝ)^s)) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity),
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add hC (by positivity),
      ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    simp only [ENNReal.ofReal_natCast]
  rw [← he] at htotal
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htotal

end Falconer

end OAI
