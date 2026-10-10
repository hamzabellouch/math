import OAI.Probability.SATComputability.PressureSigns

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

theorem relaxedFixedLogPartition_upper (n m : ℕ) [NeZero n] {β : ℝ} (hβ : 0 ≤ β) :
    relaxedFixedLogPartition n m β ≤ (n : ℝ)*Real.log 2 - β*relaxedFixedMinimum n m := by
  rw [relaxedFixedLogPartition_eq_mean, relaxedFixedMinimum]
  have h := uniformMean_mono (fun cs : Fin m → RelaxedClause n =>
    relaxedLogPartition_upper hβ (fun j => (cs j).1) (fun j => (cs j).2))
  simpa only [uniformMean_sub, uniformMean_const_mul, uniformMean_const, clauseMinimum] using h

theorem relaxedPoissonPressure_upper (n : ℕ) [NeZero n] (a : ℝ≥0)
    {β : ℝ} (hβ : 0 ≤ β) :
    relaxedPoissonPressure a β n ≤ Real.log 2 - β*(relaxedPoissonMinimum n a/n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
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
  have h := integral_mono hZ ((integrable_const _).sub (hE.const_mul β))
    (fun m => relaxedFixedLogPartition_upper n m hβ)
  simp only [Pi.sub_apply] at h
  simp only [integral_sub (integrable_const _) (hE.const_mul β), integral_const_mul,
    integral_const, probReal_univ, one_smul] at h
  have hd := div_le_div_of_nonneg_right h hn.le
  simpa only [relaxedPoissonPressure, relaxedPoissonMinimum, sub_div, mul_div_assoc,
    mul_div_cancel_left₀ _ hn.ne'] using hd

theorem negative_pressure_of_violation_density {a : ℝ≥0} (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε)
    (hV : ∀ᶠ n : ℕ in atTop, ε ≤ relaxedPoissonMinimum n a/n) :
    ∃ β : ℕ, 0 < β ∧ satPressure a β < 0 := by
  obtain ⟨β,hβ⟩ := exists_nat_gt (max 0 (Real.log 2/ε))
  have hβ0 : (0 : ℝ) < β := (le_max_left _ _).trans_lt hβ
  have hβN : 0 < β := by exact_mod_cast hβ0
  have hnegative : Real.log 2 - (β : ℝ)*ε < 0 := by
    have hgt : Real.log 2/ε < β := (le_max_right _ _).trans_lt hβ
    have hh := (div_lt_iff₀ hε).mp hgt
    linarith
  refine ⟨β,hβN,lt_of_le_of_lt ?_ hnegative⟩
  apply le_of_tendsto (relaxedPressure_tendsto ha hβ0)
  filter_upwards [hV,eventually_gt_atTop 0] with n hn hn0
  let : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  exact (relaxedPoissonPressure_upper n a hβ0.le).trans
    (sub_le_sub_left (mul_le_mul_of_nonneg_left hn hβ0.le) _)

end FixedClauseThreshold.Computability

end OAI
