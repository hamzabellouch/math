import OAI.Probability.SATComputability.SubcriticalEnergy
import OAI.Probability.SATComputability.SATVariational

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

attribute [local irreducible] relaxedLogPartition

theorem relaxedFixedLogPartition_eq_mean (n m : ℕ) (β : ℝ) :
    relaxedFixedLogPartition n m β = uniformMean
      (fun cs : Fin m → RelaxedClause n =>
        relaxedLogPartition β (fun j => (cs j).1) (fun j => (cs j).2)) := by
  let e : (Fin m → RelaxedClause n) ≃
      (Fin m → Fin 3 → Fin n) × (Fin m → Fin 3 → Bool) :=
    Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin 3 → Fin n) (fun _ => Fin 3 → Bool)
  calc
    _ = uniformMean (fun p : (Fin m → Fin 3 → Fin n) × (Fin m → Fin 3 → Bool) =>
        relaxedLogPartition β p.1 p.2) := by
      rw [uniformMean_prod, uniformMean_comm]
      rfl
    _ = uniformMean (fun cs : Fin m → RelaxedClause n =>
        relaxedLogPartition β (e cs).1 (e cs).2) :=
      (uniformMean_equiv e (fun p : (Fin m → Fin 3 → Fin n) × (Fin m → Fin 3 → Bool) =>
        relaxedLogPartition β p.1 p.2)).symm
    _ = _ := uniformMean_congr (fun _ => rfl)

theorem relaxedFixedLogPartition_lower (n m : ℕ) (β : ℝ) :
    -β * relaxedFixedMinimum n m ≤ relaxedFixedLogPartition n m β := by
  rw [relaxedFixedLogPartition_eq_mean, relaxedFixedMinimum, ← uniformMean_const_mul]
  exact uniformMean_mono (fun _ => relaxedLogPartition_lower _ _ _)

theorem relaxedFixedLogPartition_bound (n m : ℕ) [NeZero n] {β : ℝ} (hβ : 0 ≤ β) :
    |relaxedFixedLogPartition n m β| ≤ n*Real.log 2 + β*m := by
  rw [relaxedFixedLogPartition_eq_mean, abs_le]
  constructor
  · have h := uniformMean_mono (f := fun _cs : Fin m → RelaxedClause n => -(β*(m : ℝ)))
        (g := fun cs => relaxedLogPartition β (fun j => (cs j).1) (fun j => (cs j).2))
        (fun cs => ?_)
    · rw [uniformMean_const] at h
      have hl : 0 ≤ (n : ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by norm_num))
      linarith
    · have hl := relaxedLogPartition_lower β (fun j => (cs j).1) (fun j => (cs j).2)
      have hm : (clauseMinimum cs : ℝ) ≤ m := by exact_mod_cast clauseMinimum_le_length cs
      change -β * (clauseMinimum cs : ℝ) ≤ _ at hl
      exact le_trans (by nlinarith) hl
  · have h := uniformMean_mono (f := fun cs : Fin m → RelaxedClause n =>
        relaxedLogPartition β (fun j => (cs j).1) (fun j => (cs j).2))
        (g := fun _ => (n : ℝ)*Real.log 2 + β*m) (fun cs => ?_)
    · simpa only [uniformMean_const] using h
    · have hu := relaxedLogPartition_upper hβ (fun j => (cs j).1) (fun j => (cs j).2)
      have hpos := mul_nonneg hβ (Nat.cast_nonneg (clauseMinimum cs) : (0 : ℝ) ≤ _)
      nlinarith [mul_nonneg hβ (Nat.cast_nonneg m)]

theorem relaxedPoissonPressure_lower (n : ℕ) [NeZero n] (a : ℝ≥0)
    {β : ℝ} (hβ : 0 ≤ β) :
    -β * (relaxedPoissonMinimum n a / n) ≤ relaxedPoissonPressure a β n := by
  have hE : Integrable (fun m => relaxedFixedMinimum n m) (poissonMeasure (a*n)) := by
    apply (poisson_integrable_count (a*n)).mono'
      (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun m => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (relaxedFixedMinimum_nonneg n m)] using
        relaxedFixedMinimum_le n m)
  have hZ : Integrable (fun m => relaxedFixedLogPartition n m β) (poissonMeasure (a*n)) := by
    apply (((integrable_const ((n : ℝ)*Real.log 2)).add
      ((poisson_integrable_count (a*n)).const_mul β))).mono'
        (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (relaxedFixedLogPartition_bound n · hβ)
  have h := integral_mono (hE.const_mul (-β)) hZ (fun m => relaxedFixedLogPartition_lower n m β)
  rw [integral_const_mul] at h
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [relaxedPoissonMinimum, relaxedPoissonPressure, mul_div_assoc] using hd

theorem satPressure_subcritical {a : ℝ≥0} (ha : 0 < a)
    (haα : (a : ℝ) < limitingCenter 3) {β : ℝ} (hβ : 0 < β) :
    0 ≤ satPressure a β := by
  have hl := (relaxedPoissonMinimum_subcritical haα).const_mul (-β)
  have hb : ∀ᶠ n : ℕ in atTop,
      -β * (relaxedPoissonMinimum n a / n) ≤ relaxedPoissonPressure a β n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    exact relaxedPoissonPressure_lower n a hβ.le
  simpa only [mul_zero] using le_of_tendsto_of_tendsto hl (relaxedPressure_tendsto ha hβ) hb

end FixedClauseThreshold.Computability

end OAI
