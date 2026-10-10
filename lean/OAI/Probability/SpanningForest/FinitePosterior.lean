import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

variable {Θ Y : Type*} [Fintype Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] [MeasurableSpace Y]

def mixtureDensity (π : Measure Θ) (f : Θ → Y → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ∑ θ, π {θ} * f θ y

omit [MeasurableSingletonClass Θ] in
lemma measurable_mixtureDensity (π : Measure Θ) (f : Θ → Y → ℝ≥0∞)
    (hf : ∀ θ, Measurable (f θ)) : Measurable (mixtureDensity π f) := by
  unfold mixtureDensity
  fun_prop

theorem marginal_eq_withDensity (π : Measure Θ) (κ : Kernel Θ Y) (ν : Measure Y)
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) :
    κ ∘ₘ π = ν.withDensity (mixtureDensity π f) := by
  calc
    κ ∘ₘ π = Measure.sum (fun θ => π {θ} • ν.withDensity (f θ)) := by
      rw [Measure.comp_eq_sum_of_countable]
      simp_rw [hκ]
    _ = Measure.sum (fun θ => ν.withDensity (fun y => π {θ} * f θ y)) := by
      congr 1
      funext θ
      exact (withDensity_smul (π {θ}) (hf θ)).symm
    _ = ν.withDensity (∑' θ, fun y => π {θ} * f θ y) := by
      exact (withDensity_tsum (fun θ => measurable_const.mul (hf θ))).symm
    _ = ν.withDensity (mixtureDensity π f) := by
      congr 1
      ext y
      simp [mixtureDensity]

omit [MeasurableSingletonClass Θ] [MeasurableSpace Y] in
lemma mixtureDensity_ne_top (π : Measure Θ) [IsFiniteMeasure π]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ y, f θ y ≠ ∞) (y : Y) :
    mixtureDensity π f y ≠ ∞ := by
  unfold mixtureDensity
  exact ENNReal.sum_ne_top.mpr (fun θ _ => ENNReal.mul_ne_top (measure_ne_top π _) (hf θ y))

omit [MeasurableSpace Y] in

lemma mixtureDensity_ne_zero_of_positive (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ y, f θ y ≠ 0) (y : Y) :
    mixtureDensity π f y ≠ 0 := by
  have hsum : (∑ θ, π {θ}) = 1 := by simp
  have hpos : 0 < ∑ θ, π {θ} := by rw [hsum]; exact zero_lt_one
  obtain ⟨θ, hθ, hpθ⟩ := Finset.sum_pos_iff.mp hpos
  apply ne_of_gt
  exact Finset.sum_pos_iff.mpr ⟨θ, hθ, ENNReal.mul_pos hpθ.ne' (hf θ y)⟩

omit [MeasurableSingletonClass Θ] [MeasurableSpace Y] in

lemma mixtureDensity_toReal (π : Measure Θ) [IsFiniteMeasure π]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ y, f θ y ≠ ∞) (y : Y) :
    (mixtureDensity π f y).toReal = ∑ θ, (π {θ}).toReal * (f θ y).toReal := by
  rw [mixtureDensity, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro θ _
    exact ENNReal.mul_ne_top (measure_ne_top π _) (hf θ y)

theorem likelihood_rnDeriv_marginal (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ] (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) (θ : Θ) :
    (κ θ).rnDeriv (κ ∘ₘ π) =ᵐ[ν]
      fun y => f θ y / mixtureDensity π f y := by
  have hright := Measure.rnDeriv_withDensity_right (κ θ) ν
    (measurable_mixtureDensity π f hf).aemeasurable
    (Filter.Eventually.of_forall hpositive)
    (Filter.Eventually.of_forall (mixtureDensity_ne_top π f hfinite))
  have hleft : (κ θ).rnDeriv ν =ᵐ[ν] f θ := by
    rw [hκ θ]
    exact Measure.rnDeriv_withDensity ν (hf θ)
  rw [marginal_eq_withDensity π κ ν f hf hκ]
  filter_upwards [hright, hleft] with y hy hy'
  rw [hy, hy', div_eq_mul_inv, mul_comm]

theorem posterior_singleton_formula [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ] (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) :
    ∀ᵐ y ∂(κ ∘ₘ π), ∀ θ,
      (κ†π) y {θ} = π {θ} * f θ y / mixtureDensity π f y := by
  have hac : κ ∘ₘ π ≪ ν := by
    rw [marginal_eq_withDensity π κ ν f hf hκ]
    exact withDensity_absolutelyContinuous ν _
  have hrn : ∀ᵐ y ∂(κ ∘ₘ π), ∀ θ,
      (κ θ).rnDeriv (κ ∘ₘ π) y = f θ y / mixtureDensity π f y := by
    exact hac.ae_le (ae_all_iff.mpr (fun θ =>
      likelihood_rnDeriv_marginal π κ ν f hf hfinite hpositive hκ θ))
  filter_upwards [posterior_eq_withDensity_of_countable κ π, hrn] with y hy hrny
  intro θ
  rw [hy]
  simp only [withDensity_apply _ (measurableSet_singleton θ), lintegral_singleton, hrny θ]
  rw [mul_comm, mul_div_assoc]

theorem posterior_mean_formula [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ] (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) (g : Θ → ℝ) :
    ∀ᵐ y ∂(κ ∘ₘ π),
      (∫ θ, g θ ∂(κ†π) y) =
        (∑ θ, (π {θ}).toReal * (f θ y).toReal * g θ) /
          (mixtureDensity π f y).toReal := by
  filter_upwards [posterior_singleton_formula π κ ν f hf hfinite hpositive hκ]
    with y hy
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real, hy, ENNReal.toReal_div, ENNReal.toReal_mul, smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  exact (Finset.sum_div _ _ _).symm

theorem condExp_eq_posterior_mean [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ] (g : Θ → ℝ) :
    (π ⊗ₘ κ)[fun z : Θ × Y => g z.1 |
      (inferInstance : MeasurableSpace Y).comap Prod.snd] =ᵐ[π ⊗ₘ κ]
      fun z => ∫ θ, g θ ∂(κ†π) z.2 := by
  have hgint : Integrable (fun z : Θ × Y => g z.1) (π ⊗ₘ κ) :=
    (show Integrable g ((π ⊗ₘ κ).map Prod.fst) from Integrable.of_finite).comp_measurable
      measurable_fst
  have h := condExp_ae_eq_integral_condDistrib (μ := π ⊗ₘ κ)
    measurable_snd measurable_fst.aemeasurable
    (measurable_of_countable g).stronglyMeasurable hgint
  have hkernel : condDistrib (Prod.fst : Θ × Y → Θ) Prod.snd (π ⊗ₘ κ) = κ†π := by
    rw [condDistrib, posterior]
    congr 1
  rwa [hkernel] at h

theorem condExp_eq_likelihood_ratio [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ] (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) (g : Θ → ℝ) :
    (π ⊗ₘ κ)[fun z : Θ × Y => g z.1 |
      (inferInstance : MeasurableSpace Y).comap Prod.snd] =ᵐ[π ⊗ₘ κ]
      fun z => (∑ θ, (π {θ}).toReal * (f θ z.2).toReal * g θ) /
        (mixtureDensity π f z.2).toReal := by
  apply (condExp_eq_posterior_mean π κ g).trans
  have hpost := posterior_mean_formula π κ ν f hf hfinite hpositive hκ g
  have hmap : (π ⊗ₘ κ).map Prod.snd = κ ∘ₘ π := Measure.snd_compProd π κ
  rw [← hmap] at hpost
  exact ae_of_ae_map (μ := π ⊗ₘ κ) (f := Prod.snd) measurable_snd.aemeasurable hpost

theorem condExp_eq_posterior_mean_of_jointLaw
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Yobs : Ω → Y) (hX : Measurable X) (hY : Measurable Yobs)
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ]
    (hjoint : P.map (fun ω => (X ω, Yobs ω)) = π ⊗ₘ κ) (g : Θ → ℝ) :
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace Y).comap Yobs] =ᵐ[P]
      fun ω => ∫ θ, g θ ∂(κ†π) (Yobs ω) := by
  have hmapY : P.map Yobs = κ ∘ₘ π := by
    calc
      P.map Yobs = (P.map (fun ω => (X ω, Yobs ω))).map Prod.snd := by
        rw [Measure.map_map measurable_snd (hX.prodMk hY)]
        rfl
      _ = (π ⊗ₘ κ).snd := by rw [hjoint]; rfl
      _ = κ ∘ₘ π := Measure.snd_compProd π κ
  have hswap : P.map (fun ω => (Yobs ω, X ω)) = (π ⊗ₘ κ).map Prod.swap := by
    rw [← hjoint, Measure.map_map measurable_swap (hX.prodMk hY)]
    rfl
  have hkernel : condDistrib X Yobs P =ᵐ[P.map Yobs] κ†π := by
    apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hY hX
    rw [hmapY, compProd_posterior_eq_map_swap]
    exact hswap
  have hgint : Integrable (fun ω => g (X ω)) P :=
    (show Integrable g (P.map X) from Integrable.of_finite).comp_measurable hX
  have hcond := condExp_ae_eq_integral_condDistrib hY hX.aemeasurable
    (measurable_of_countable g).stronglyMeasurable hgint
  have hkernel' := ae_of_ae_map hY.aemeasurable hkernel
  filter_upwards [hcond, hkernel'] with ω hω hkω
  rwa [hkω] at hω

theorem condExp_eq_likelihood_ratio_of_jointLaw
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Yobs : Ω → Y) (hX : Measurable X) (hY : Measurable Yobs)
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ]
    (hjoint : P.map (fun ω => (X ω, Yobs ω)) = π ⊗ₘ κ)
    (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) (g : Θ → ℝ) :
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace Y).comap Yobs] =ᵐ[P]
      fun ω => (∑ θ, (π {θ}).toReal * (f θ (Yobs ω)).toReal * g θ) /
        (mixtureDensity π f (Yobs ω)).toReal := by
  apply (condExp_eq_posterior_mean_of_jointLaw P X Yobs hX hY π κ hjoint g).trans
  have hmapY : P.map Yobs = κ ∘ₘ π := by
    calc
      P.map Yobs = (P.map (fun ω => (X ω, Yobs ω))).map Prod.snd := by
        rw [Measure.map_map measurable_snd (hX.prodMk hY)]
        rfl
      _ = (π ⊗ₘ κ).snd := by rw [hjoint]; rfl
      _ = κ ∘ₘ π := Measure.snd_compProd π κ
  have hpost := posterior_mean_formula π κ ν f hf hfinite hpositive hκ g
  rw [← hmapY] at hpost
  exact ae_of_ae_map hY.aemeasurable hpost

end Problem336.FinitePosterior

end

end OAI
