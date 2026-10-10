import OAI.Geometry.TranslativeCovering.RadialIntegral

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace WeightedVolume
open Set MeasureTheory Metric
open scoped ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
lemma deficit_lintegral {n : ℕ} [NeZero n] {a : ℝ} (ha : 0<a) :
    ∫⁻ x : Space n,ENNReal.ofReal (max (1-‖x‖^2/a^2) 0) =
      ENNReal.ofReal (2/((n:ℝ)+2))*volume (closedBall (0:Space n) a) := by
  have hV : 0 < volume.real (closedBall (0:Space n) a) := by
    exact ENNReal.toReal_pos (measure_closedBall_pos volume (0:Space n) ha).ne'
      (isCompact_closedBall (0:Space n) a).measure_ne_top
  have hi := RadialIntegral.deficit_integral (n := n) ha
  have hint : Integrable (fun x : Space n => max (1-‖x‖^2/a^2) 0) volume :=
    Integrable.of_integral_ne_zero (by rw [hi]; positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun x => le_max_right _ _)),hi,
    ENNReal.ofReal_mul (by positivity),Measure.real,ENNReal.ofReal_toReal (isCompact_closedBall (0:Space n) a).measure_ne_top]
lemma weighted_lintegral {n : ℕ} [NeZero n] {a β : ℝ} (ha : 0<a) :
    ∫⁻ x : Space n,LocalizationGood.weightedFn a β x ≤
      volume (closedBall (0:Space n) β)+2*volume (closedBall (0:Space n) a) := by
  let δ (x : Space n) := ENNReal.ofReal (max (1-‖x‖^2/a^2) 0)
  have hδ : Measurable δ := by dsimp [δ]; fun_prop
  have hpoint (x : Space n) : LocalizationGood.weightedFn a β x ≤
      LocalizationGood.countFn (closedBall (0:Space n) β) x+(n:ℝ≥0∞)*δ x := by
    by_cases hx : x ∈ closedBall (0:Space n) β
    · rw [LocalizationGood.weightedFn,Set.indicator_of_mem hx,
        LocalizationGood.countFn,Set.indicator_of_mem hx]
      change ENNReal.ofReal (1+(n:ℝ)*max (1-‖x‖^2/a^2) 0) ≤
        1+(n:ℝ≥0∞)*ENNReal.ofReal (max (1-‖x‖^2/a^2) 0)
      rw [ENNReal.ofReal_add (by norm_num : (0:ℝ)≤1)
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (le_max_right _ _)),
        ENNReal.ofReal_one,ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) n),ENNReal.ofReal_natCast]
    · simp only [LocalizationGood.weightedFn,LocalizationGood.countFn,Set.indicator_of_notMem hx,zero_add]
      exact bot_le
  apply (lintegral_mono hpoint).trans
  unfold LocalizationGood.countFn
  rw [lintegral_add_left (measurable_const.indicator measurableSet_closedBall),
    lintegral_const_mul _ hδ]
  simp only [lintegral_indicator measurableSet_closedBall,lintegral_const,Measure.restrict_apply_univ,one_mul]
  change volume (closedBall (0:Space n) β)+(n:ℝ≥0∞)*(∫⁻ x : Space n,ENNReal.ofReal (max (1-‖x‖^2/a^2) 0)) ≤ _
  rw [deficit_lintegral ha]
  have hnum : (n:ℝ≥0∞)*ENNReal.ofReal (2/((n:ℝ)+2)) ≤ 2 := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) n)]
    have hh : (n:ℝ)*(2/((n:ℝ)+2)) ≤ 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)).mpr
      nlinarith only [Nat.cast_nonneg (α := ℝ) n]
    simpa using ENNReal.ofReal_le_ofReal hh
  calc
    _ = volume (closedBall (0:Space n) β)+((n:ℝ≥0∞)*ENNReal.ofReal (2/((n:ℝ)+2)))*volume (closedBall (0:Space n) a) := by rw [mul_assoc]
    _ ≤ _ := by gcongr
end WeightedVolume

end OAI
