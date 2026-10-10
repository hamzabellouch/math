import OAI.Probability.FreeIsing.Martingales.ContinuousSelection
import OAI.Probability.FreeIsing.Martingales.StrongMaximal

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MartingaleRandomEvaluation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stronglyMeasurable_random_evaluation
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hp : IsStronglyProgressive F M) {τ : Ω → ℝ≥0} (hτ : Measurable τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    StronglyMeasurable (fun ω => M (τ ω) ω) := by
  have hm : StronglyMeasurable (fun p : Iic T × Ω => M p.1 p.2) :=
    (hp T).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le T)))
  let τ' : Ω → Iic T := fun ω => ⟨τ ω, hbound ω⟩
  have ht : Measurable τ' := hτ.subtype_mk
  exact hm.comp_measurable (ht.prodMk measurable_id)

theorem aestronglyMeasurable_random_evaluation
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted F M)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    AEStronglyMeasurable (fun ω => M (τ ω) ω) P := by
  have hm := stronglyMeasurable_random_evaluation
    (PredictableMesh.repair_isStronglyPredictable hM).isStronglyProgressive hτ hbound
  apply hm.aestronglyMeasurable.congr
  filter_upwards [hc] with ω hω
  exact PredictableMesh.repair_eq_of_continuousOn (T := τ ω) hω.continuousOn le_rfl

theorem integrable_sq_random_evaluation [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => M (τ ω) ω ^ 2) P := by
  apply (MartingaleStrongMaximal.integrable_maximalSquare hM h2 hc T).mono'
    ((aestronglyMeasurable_random_evaluation hM.stronglyAdapted hc hτ hbound).pow 2)
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM h2 hc T] with ω hω
  change ‖M (τ ω) ω ^ 2‖ ≤ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (M (τ ω) ω))] using
    hω (τ ω) (hbound ω)

theorem memLp_random_evaluation [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    MemLp (fun ω => M (τ ω) ω) 2 P :=
  (memLp_two_iff_integrable_sq
    (aestronglyMeasurable_random_evaluation hM.stronglyAdapted hc hτ hbound)).mpr
      (integrable_sq_random_evaluation hM h2 hc hτ hbound)

theorem integral_sq_random_evaluation_le [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    (∫ ω, M (τ ω) ω ^ 2 ∂P) ≤ 4 * ∫ ω, M T ω ^ 2 ∂P := by
  apply le_trans (integral_mono_ae
    (integrable_sq_random_evaluation hM h2 hc hτ hbound)
    (MartingaleStrongMaximal.integrable_maximalSquare hM h2 hc T) ?_)
    (MartingaleStrongMaximal.integral_maximalSquare_le hM h2 hc T)
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM h2 hc T] with ω hω
  exact hω (τ ω) (hbound ω)

theorem tendsto_integral_sq_random_evaluation_sub [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ} {L : ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F P) (hL : Martingale L F P)
    (h2 : ∀ n t, MemLp (M n t) 2 P) (hL2 : ∀ t, MemLp (L t) 2 P)
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => M n t ω))
    (hLc : ∀ᵐ ω ∂P, Continuous (fun t => L t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T)
    (hlim : Tendsto (fun n => ∫ ω, (M n T ω - L T ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (M n (τ ω) ω - L (τ ω) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hdiff (n : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t => (M n - L) t ω) := by
    filter_upwards [hc n, hLc] with ω hm hl
    exact hm.sub hl
  apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _))
    (fun n => ?_) (by simpa only [mul_zero] using hlim.const_mul 4)
  simpa only [Pi.sub_apply] using integral_sq_random_evaluation_le
    ((hM n).sub hL) (fun t => (h2 n t).sub (hL2 t)) (hdiff n) hτ hbound

end Problem367.MartingaleRandomEvaluation

end

end OAI
