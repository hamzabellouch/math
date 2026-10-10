import OAI.Probability.DilutedSpin.PhysicalIndex

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

/-- Integrate a deterministic logarithmic stability estimate without imposing
moments beyond the integrable envelope. -/
theorem probabilistic_center_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f g : X → ℝ} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hb : ∀ᵐ x ∂μ, |f x-c| ≤ g x) :
    Integrable f μ ∧ |(∫ x, f x ∂μ)-c| ≤ ∫ x, g x ∂μ := by
  have hfc : Integrable (fun x => f x-c) μ :=
    hg.mono' (hf.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using hb)
  have hfi : Integrable f μ := by
    simpa only [Pi.add_def, sub_add_cancel] using hfc.add (integrable_const c)
  refine ⟨hfi, ?_⟩
  have hi : (∫ x, f x ∂μ)-c = ∫ x, f x-c ∂μ := by
    rw [integral_sub hfi (integrable_const c)]
    simp
  rw [hi]
  exact abs_integral_le_integral_abs.trans (integral_mono_ae hfc.abs hg hb)

noncomputable def fieldAverage {p : ℕ} (M : Model p) {N k : ℕ}
    (theta : Fin k → InteractionSample p) : ℝ :=
  ∫ h : Fin N → ℝ, indexAverage theta h ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)

noncomputable def disorderAverage {p : ℕ} (M : Model p) (N k : ℕ) : ℝ :=
  ∫ theta : Fin k → InteractionSample p, fieldAverage M (N := N) theta
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)

noncomputable def interactionMoment {p : ℕ} (M : Model p) : ℝ :=
  ∫ z : InteractionSample p, ‖z.1‖ ∂M.disorder.toMeasure

noncomputable def fieldMoment {p : ℕ} (M : Model p) : ℝ :=
  ∫ h : ℝ, |h| ∂M.field.toMeasure

theorem indexAverage_integrable_and_fieldAverage_bound {p : ℕ} (M : Model p)
    (hM : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N k : ℕ}
    (hN : 0 < N) (theta : Fin k → InteractionSample p) :
    Integrable (fun h : Fin N → ℝ => indexAverage theta h)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) ∧
    |fieldAverage M (N := N) theta - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + N * fieldMoment M := by
  have hi : Integrable (fun h : Fin N → ℝ => ∑ i, |h i|)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) := by
    exact integrable_finsetSum _ (fun i _ => integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM)
  have he : (∫ h : Fin N → ℝ, (∑ j, ‖(theta j).1‖) + ∑ i, |h i|
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)) =
        (∑ j, ‖(theta j).1‖) + N * fieldMoment M := by
    rw [integral_add (integrable_const _) hi, integral_finsetSum _
      (fun i _ => integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM)]
    simp only [integral_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hM.aestronglyMeasurable]
    simp [fieldMoment]
  have hm : AEStronglyMeasurable (fun h : Fin N → ℝ => indexAverage theta h)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) :=
    (continuous_indexAverage.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  simpa only [fieldAverage, Pi.add_apply, he] using probabilistic_center_bound
    (Measure.pi (fun _ : Fin N => M.field.toMeasure)) hm
      ((integrable_const _).add hi) (ae_of_all _ (indexAverage_bound hN theta))

theorem stronglyMeasurable_fieldAverage {p : ℕ} (M : Model p) (N k : ℕ) :
    StronglyMeasurable (fieldAverage M (N := N) (k := k)) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact (continuous_indexAverage (p := p) (N := N) (k := k)).stronglyMeasurable.integral_prod_right

theorem fieldAverage_integrable_and_disorderAverage_bound {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N : ℕ}
    (hN : 0 < N) (k : ℕ) :
    Integrable (fieldAverage M (N := N) (k := k))
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) ∧
    |disorderAverage M N k - (N:ℝ)*Real.log 2| ≤
      k * interactionMoment M + N * fieldMoment M := by
  have hi : Integrable (fun theta : Fin k → InteractionSample p => ∑ j, ‖(theta j).1‖)
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) :=
    integrable_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)
  have he : (∫ theta : Fin k → InteractionSample p,
      (∑ j, ‖(theta j).1‖) + N * fieldMoment M
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
        k * interactionMoment M + N * fieldMoment M := by
    rw [integral_add hi (integrable_const _), integral_finsetSum _
      (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)]
    simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ.aestronglyMeasurable]
    simp [interactionMoment]
  simpa only [disorderAverage, Pi.add_apply, he] using probabilistic_center_bound
    (Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
      (stronglyMeasurable_fieldAverage M N k).aestronglyMeasurable
      (hi.add (integrable_const _)) (ae_of_all _ (fun theta =>
        (indexAverage_integrable_and_fieldAverage_bound M hh hN theta).2))


theorem disorderAverage_integrable_and_pressure_bound {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) {N : ℕ} (hN : 0 < N) :
    Integrable (disorderAverage M N) (poissonMeasure (M.alpha * N)) ∧
      |pressure M N - Real.log 2| ≤ (M.alpha:ℝ) * interactionMoment M + fieldMoment M := by
  have hi : Integrable (fun k : ℕ => (k:ℝ) * interactionMoment M + N * fieldMoment M)
      (poissonMeasure (M.alpha * N)) :=
    ((poisson_integrable_count _).mul_const _).add (integrable_const _)
  have he : (∫ k : ℕ, (k:ℝ) * interactionMoment M + N * fieldMoment M
      ∂poissonMeasure (M.alpha * N)) =
      ((M.alpha:ℝ)*N) * interactionMoment M + N * fieldMoment M := by
    rw [integral_add ((poisson_integrable_count _).mul_const _) (integrable_const _),
      integral_mul_const, poisson_mean]
    simp
  have hb := probabilistic_center_bound (poissonMeasure (M.alpha * N))
    (f := disorderAverage M N) (c := (N:ℝ)*Real.log 2)
    StronglyMeasurable.of_discrete.aestronglyMeasurable hi
    (ae_of_all _ (fun k => (fieldAverage_integrable_and_disorderAverage_bound M hθ hh hN k).2))
  refine ⟨hb.1, ?_⟩
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hp : pressure M N = (∫ k, disorderAverage M N k ∂poissonMeasure (M.alpha * N)) / N := rfl
  rw [hp, div_sub' (ne_of_gt hNr), abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  rw [he] at hb
  nlinarith [hb.2]


end DilutedSpinGlass
end

end

end OAI
