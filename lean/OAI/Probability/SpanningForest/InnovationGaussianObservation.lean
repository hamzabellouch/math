import OAI.Probability.SpanningForest.InnovationAdapted

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem336.Innovation

theorem integral_gaussian_on_independent_past
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hm : m ≤ mΩ) {Q : Ω → ℝ} {v : ℝ≥0}
    (hQ : HasLaw Q (gaussianReal 0 v) P) (hQmeas : Measurable Q)
    (hindep : Indep (MeasurableSpace.comap Q (inferInstance : MeasurableSpace ℝ)) m P)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    (∫ ω in A, Q ω ∂P) = 0 := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  have hmean : (∫ ω, Q ω ∂P) = 0 := by
    rw [hQ.integral_eq, integral_id_gaussianReal]
  have hcond : P[Q | m] =ᵐ[P] fun _ => (0 : ℝ) := by
    simpa only [hmean] using condExp_indep_eq hQmeas.comap_le hm
      (comap_measurable Q).stronglyMeasurable hindep
  rw [← setIntegral_condExp hm hQ.hasGaussianLaw.integrable hA]
  calc
    (∫ ω in A, P[Q | m] ω ∂P) = ∫ _ in A, (0 : ℝ) ∂P :=
      integral_congr_ae (ae_restrict_of_ae hcond)
    _ = 0 := by simp

theorem martingale_borel_observation_of_gaussian_increments
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i))
    (i : ι) (X : Ω → ℝ) (hXmeas : Measurable X)
    (hXbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1)
    (B : ℝ≥0 → Ω → ℝ)
    (hobs : ∀ t ω, Y t ω i = (t : ℝ) * X ω + B t ω)
    (hBzero : B 0 =ᵐ[P] 0)
    (hinc : ∀ u v : ℝ≥0, u ≤ v →
      HasLaw (fun ω => B v ω - B u ω) (gaussianReal 0 (v - u)) P)
    (hindep : ∀ u v : ℝ≥0, u ≤ v →
      Indep (MeasurableSpace.comap (fun ω => B v ω - B u ω)
        (inferInstance : MeasurableSpace ℝ)) (ℱ u) P)
    (b : ℝ≥0 → (ι → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hbound : ∀ t y, ‖b t y‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, (fun ω => b t (Y t ω)) =ᵐ[P] P[X | ℱ t]) :
    Martingale (fun t ω => Y t ω i -
      ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) ℱ P := by
  let : IsProbabilityMeasure P := (hinc 0 0 le_rfl).isProbabilityMeasure
  have hX : Integrable X P := Integrable.of_bound hXmeas.aestronglyMeasurable 1 (by
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hXbound ω).1]
    exact (hXbound ω).2)
  have hBmeas (t : ℝ≥0) : Measurable (B t) := by
    have heq : B t = fun ω => Y t ω i - (t : ℝ) * X ω := by
      funext ω
      rw [hobs]
      ring
    rw [heq]
    exact ((hadapted t i).mono (ℱ.le t) le_rfl).sub (measurable_const.mul hXmeas)
  have hB (t : ℝ≥0) : Integrable (B t) P := by
    have hlaw : HasLaw (B t) (gaussianReal 0 t) P := by
      have hzero := (hinc 0 t (by exact zero_le)).congr (show
          B t =ᵐ[P] fun ω => B t ω - B 0 ω from by
        filter_upwards [hBzero] with ω hω
        simp only [Pi.zero_apply] at hω
        rw [hω, sub_zero])
      simpa only [tsub_zero] using hzero
    exact hlaw.hasGaussianLaw.integrable
  apply martingale_borel_observation P ℱ Y hcont hadapted i X B hobs hX hB b hb
    hbound hposterior
  intro u v huv A hA
  exact integral_gaussian_on_independent_past (ℱ.le u) (hinc u v huv)
    ((hBmeas v).sub (hBmeas u)) (hindep u v huv) hA

end Problem336.Innovation

end

end OAI
