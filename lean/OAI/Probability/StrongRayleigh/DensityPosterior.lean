import Mathlib

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Problem336AdditiveD139.DensityPosterior

variable {S : Type u_1} {Y : Type u_2} [MeasurableSpace S] [MeasurableSpace Y]
  {μ : Measure S} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem condExp_snd_of_fiber_integral
    {ρ : Measure (S × Y)} [IsFiniteMeasure ρ]
    {w : S × Y → ℝ} (hw : Measurable w) (hw0 : ∀ p, 0 ≤ w p)
    (hρ : ρ = (μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))
    {f : S → ℝ} {g : Y → ℝ} (hg : Measurable g)
    (hf : Integrable (fun p : S × Y => f p.1) ρ)
    (hgint : Integrable (fun p : S × Y => g p.2) ρ)
    (hfiber : ∀ᵐ y ∂ν, (∫ s, w (s,y) * f s ∂μ) = ∫ s, w (s,y) * g y ∂μ) :
    ρ[(fun p : S × Y => f p.1) | MeasurableSpace.comap Prod.snd inferInstance]
      =ᵐ[ρ] fun p => g p.2 := by
  have hwf : Integrable (fun p : S × Y => w p * f p.1) (μ.prod ν) := by
    have h := (integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp (hρ ▸ hf)
    simpa only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul] using h
  have hwg : Integrable (fun p : S × Y => w p * g p.2) (μ.prod ν) := by
    have h := (integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp (hρ ▸ hgint)
    simpa only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul] using h
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_snd.comap_le hf
    (fun A _ _ => hgint.integrableOn) ?_
    ((hg.comp (comap_measurable Prod.snd)).stronglyMeasurable.aestronglyMeasurable)
  intro A hA hρA
  rcases hA with ⟨B, hB, rfl⟩
  have hpre : (Prod.snd : S × Y → Y) ⁻¹' B = Set.univ ×ˢ B := by ext p; simp
  rw [hpre, hρ]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hw.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ (MeasurableSet.univ.prod hB),
    setIntegral_withDensity_eq_setIntegral_toReal_smul hw.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ (MeasurableSet.univ.prod hB)]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  have hwgB : Integrable (fun p : S × Y => w p * g p.2) (μ.prod (ν.restrict B)) :=
    hwg.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hwfB : Integrable (fun p : S × Y => w p * f p.1) (μ.prod (ν.restrict B)) :=
    hwf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [integral_prod_symm _ hwgB, integral_prod_symm _ hwfB]
  exact integral_congr_ae (ae_restrict_of_ae (hfiber.mono fun _ h => h.symm))

def posteriorRatio (μ : Measure S) (w : S × Y → ℝ) (f : S → ℝ) (y : Y) : ℝ :=
  (∫ s, w (s, y) * f s ∂μ) / ∫ s, w (s, y) ∂μ

theorem condExp_snd_eq_posteriorRatio
    {ρ : Measure (S × Y)} [IsFiniteMeasure ρ]
    {w : S × Y → ℝ} (hw : Measurable w) (hw0 : ∀ p, 0 ≤ w p)
    (hρ : ρ = (μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))
    (hwi : ∀ y, Integrable (fun s => w (s,y)) μ)
    (hpos : ∀ y, 0 < ∫ s, w (s,y) ∂μ)
    {f : S → ℝ} (hf : Measurable f) (hfrange : ∀ s, 0 ≤ f s ∧ f s ≤ 1) :
    ρ[(fun p : S × Y => f p.1) | MeasurableSpace.comap Prod.snd inferInstance]
      =ᵐ[ρ] fun p => posteriorRatio μ w f p.2 := by
  have hfbound : ∀ s, |f s| ≤ 1 := fun s => by
    rw [abs_of_nonneg (hfrange s).1]
    exact (hfrange s).2
  have hnumi (y : Y) : Integrable (fun s => w (s,y) * f s) μ :=
    (hwi y).mul_bdd hf.aestronglyMeasurable
      (Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hfbound s)
  have hgrange (y : Y) : 0 ≤ posteriorRatio μ w f y ∧ posteriorRatio μ w f y ≤ 1 := by
    have hnum0 : 0 ≤ ∫ s, w (s,y) * f s ∂μ :=
      integral_nonneg (fun s => mul_nonneg (hw0 _) (hfrange s).1)
    have hnumle : (∫ s, w (s,y) * f s ∂μ) ≤ ∫ s, w (s,y) ∂μ :=
      integral_mono (hnumi y) (hwi y)
        (fun s => mul_le_of_le_one_right (hw0 _) (hfrange s).2)
    exact ⟨div_nonneg hnum0 (hpos y).le, (div_le_one (hpos y)).2 hnumle⟩
  have hg : Measurable (posteriorRatio μ w f) := by
    exact (hw.mul (hf.comp measurable_fst)).stronglyMeasurable.integral_prod_left'.measurable.div
      hw.stronglyMeasurable.integral_prod_left'.measurable
  have hfi : Integrable (fun p : S × Y => f p.1) ρ :=
    Integrable.of_bound (hf.comp measurable_fst).aestronglyMeasurable 1
      (Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hfbound p.1)
  have hgi : Integrable (fun p : S × Y => posteriorRatio μ w f p.2) ρ := by
    apply Integrable.of_bound (hg.comp measurable_snd).aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, Function.comp_apply, abs_of_nonneg (hgrange p.2).1]
      exact (hgrange p.2).2
  apply condExp_snd_of_fiber_integral hw hw0 hρ hg hfi hgi
  exact Eventually.of_forall fun y => by
    rw [integral_mul_const]
    unfold posteriorRatio
    field_simp [(hpos y).ne']

theorem finite_condExp_snd_eq_posteriorRatio
    [Finite S] [MeasurableSingletonClass S] [IsProbabilityMeasure μ]
    {ρ : Measure (S × Y)} [IsFiniteMeasure ρ]
    {w : S × Y → ℝ} (hw : Measurable w) (hwpos : ∀ p, 0 < w p)
    (hρ : ρ = (μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))
    {f : S → ℝ} (hfrange : ∀ s, 0 ≤ f s ∧ f s ≤ 1) :
    ρ[(fun p : S × Y => f p.1) | MeasurableSpace.comap Prod.snd inferInstance]
      =ᵐ[ρ] fun p => posteriorRatio μ w f p.2 := by
  apply condExp_snd_eq_posteriorRatio hw (fun p => (hwpos p).le) hρ
    (fun _ => Integrable.of_finite) _ (measurable_of_finite _) hfrange
  intro y
  apply (integral_pos_iff_support_of_nonneg (fun s => (hwpos (s,y)).le)
    Integrable.of_finite).2
  have hs : Function.support (fun s => w (s,y)) = Set.univ := by
    ext s
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hwpos (s,y)).ne'
  simp [hs]

omit [MeasurableSpace Y] [SFinite μ] in

theorem posteriorRatio_eq_sum [Fintype S] [MeasurableSingletonClass S]
    [IsFiniteMeasure μ] (w : S × Y → ℝ) (f : S → ℝ) (y : Y) :
    posteriorRatio μ w f y =
      (∑ s, μ.real {s} * (w (s,y) * f s)) / (∑ s, μ.real {s} * w (s,y)) := by
  rw [posteriorRatio, integral_fintype Integrable.of_finite,
    integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]

end Problem336AdditiveD139.DensityPosterior

end

end OAI
