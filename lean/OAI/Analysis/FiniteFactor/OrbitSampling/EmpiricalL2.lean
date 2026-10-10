import OAI.Analysis.FiniteFactor.OrbitSampling.ErrorEvent

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical
noncomputable section

theorem sourceSamplingEmpiricalDensity_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (θ : SourceCoordinate → ℝ) : Measurable (sourceSamplingEmpiricalDensity stage r b E G θ) :=
  (Finset.measurable_sum _ (fun n _ => (sourceSamplingProduct_measurable stage r b E G hE hG n).comp
    (measurable_const.prodMk measurable_id))).div_const _

/-- Every empirical density is bounded at its finite stage, including stages
whose selected set is empty. No asymptotic assumption is used here. -/
theorem sourceSamplingEmpiricalDensity_bounds (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingEmpiricalDensity stage r b E G θ x ∧
      sourceSamplingEmpiricalDensity stage r b E G θ x ≤
        (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card := by
  let C := (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card
  have hC : 0 ≤ C := pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)) _
  have hb := sourceSamplingProduct_bounds stage r b E G
  have hn : 0 ≤ sourceSamplingEmpiricalDensity stage r b E G θ x :=
    div_nonneg (sum_nonneg (fun n _ => (hb n θ x).1)) (by positivity)
  refine ⟨hn,?_⟩
  by_cases hS : (sourceSamplingPowers stage).Nonempty
  · have hP : (0 : ℝ) < (sourceSamplingPowers stage).card := by exact_mod_cast hS.card_pos
    apply (div_le_iff₀ hP).mpr
    calc
      _ ≤ ∑ _n ∈ sourceSamplingPowers stage, C := sum_le_sum (fun n _ => (hb n θ x).2)
      _ = _ := by simp [C]; ring
  · have he : sourceSamplingPowers stage = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [sourceSamplingEmpiricalDensity,he]

/-- The empirical densities, not only the ideal products, belong to L2. -/
theorem sourceSamplingEmpiricalDensity_memLp (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (θ : SourceCoordinate → ℝ) :
    MemLp (sourceSamplingEmpiricalDensity stage r b E G θ) 2
      (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) := by
  apply MemLp.of_bound (sourceSamplingEmpiricalDensity_measurable stage r b E G hE hG θ).aestronglyMeasurable
    ((max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sourceSamplingEmpiricalDensity_bounds stage r b E G θ x).1]
  exact (sourceSamplingEmpiricalDensity_bounds stage r b E G θ x).2

/-- The full error and the ideal L2 bound control the actual empirical square. -/
theorem sourceSamplingEmpiricalDensity_square_le (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (θ : SourceCoordinate → ℝ) :
    (∫ x, sourceSamplingEmpiricalDensity stage r b E G θ x^2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤
      2*sourceSamplingSquaredError stage r b E G θ+2*Real.exp 5 := by
  let μ := Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)
  let z := sourceSamplingEmpiricalDensity stage r b E G θ
  let g := sourceSamplingIdealDensity stage r b E G
  let C := (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card
  have hz := sourceSamplingEmpiricalDensity_measurable stage r b E G hE hG θ
  have hg := sourceSamplingIdealDensity_measurable stage r b E G hE hG
  have hzb := sourceSamplingEmpiricalDensity_bounds stage r b E G θ
  have hgb := sourceSamplingIdealDensity_bounds stage r b E G hE hG
  have hzi : Integrable (fun x => z x^2) μ := sampling_square_integrable μ z C hz hzb
  have hgi : Integrable (fun x => g x^2) μ := sampling_square_integrable μ g C hg hgb
  have hei : Integrable (fun x => (z x-g x)^2) μ := by
    apply sampling_integrable_bounded μ _ ((hz.sub hg).pow_const 2) (C^2)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hz' : 0 ≤ z x ∧ z x ≤ C := hzb x
    have hg' : 0 ≤ g x ∧ g x ≤ C := hgb x
    change (z x-g x)^2 ≤ C^2
    nlinarith [mul_nonneg (show 0 ≤ C-(z x-g x) by linarith) (show 0 ≤ C+(z x-g x) by linarith)]
  have hi := integral_mono_ae hzi ((hei.const_mul 2).add (hgi.const_mul 2))
    (Eventually.of_forall (fun x => show z x^2 ≤ 2*(z x-g x)^2+2*g x^2 by nlinarith [sq_nonneg (z x-2*g x)]))
  simp only [Pi.add_apply] at hi
  rw [integral_add (hei.const_mul 2) (hgi.const_mul 2),integral_const_mul,integral_const_mul] at hi
  exact hi.trans (by
    have hb := sourceSamplingIdealDensity_uniform_square stage r b E G hE hG
    change (∫ x, g x^2 ∂μ) ≤ Real.exp 5 at hb
    change _ ≤ 2*(∫ x, (z x-g x)^2 ∂μ)+2*Real.exp 5
    linarith)

end
end FiniteFactor

end OAI
