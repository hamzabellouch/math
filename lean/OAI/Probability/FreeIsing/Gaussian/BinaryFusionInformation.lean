import OAI.Probability.FreeIsing.Gaussian.BinaryFusionPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def binaryFusionLaw (μ ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  (μ.prod ν).withDensity (fun z => ENNReal.ofReal (1 + z.1 * z.2))

private theorem ae_binaryFusion_support (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, |u| < 1) (hν : ∀ᵐ v ∂ν, |v| < 1) :
    ∀ᵐ z ∂μ.prod ν, |z.1| < 1 ∧ |z.2| < 1 := by
  have hfst := (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hμ
  have hsnd := (measurePreserving_snd (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hν
  filter_upwards [hfst, hsnd] with z hu hv
  exact ⟨hu, hv⟩

theorem binaryFusionLoss_le_sum_squares {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    binaryFusionLoss u v ≤ u ^ 2 + v ^ 2 := by
  have hp := binaryFusion_denominator_pos hu hv
  have hm := binaryFusion_denominator_pos hu (by simpa using hv : |-v| < 1)
  have heq := binaryFusion_symmetric_square hu hv
  have hnonneg : 0 ≤ ((u + v) ^ 2 / (1 + u * v) +
      (u - v) ^ 2 / (1 - u * v)) / 2 := by
    have hm' : 0 < 1 - u * v := by simpa using hm
    positivity
  linarith

private theorem integrable_binaryFusion_integrand (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, |u| < 1) (hν : ∀ᵐ v ∂ν, |v| < 1) :
    Integrable (fun z : ℝ × ℝ => (z.1 + z.2)^2 / (1 + z.1 * z.2)) (μ.prod ν) := by
  apply Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 2
  filter_upwards [ae_binaryFusion_support μ ν hμ hν] with z hz
  have hd := binaryFusion_denominator_pos hz.1 hz.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (z.1 + z.2)^2 / (1 + z.1 * z.2))]
  exact binaryFusion_integrand_le_two hz.1 hz.2

theorem integrable_binaryFusionLoss_product (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, |u| < 1) (hν : ∀ᵐ v ∂ν, |v| < 1) :
    Integrable (fun z : ℝ × ℝ => binaryFusionLoss z.1 z.2) (μ.prod ν) := by
  apply Integrable.of_bound (Measurable.aestronglyMeasurable (by unfold binaryFusionLoss; fun_prop)) 2
  filter_upwards [ae_binaryFusion_support μ ν hμ hν] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (binaryFusionLoss_nonneg hz.1 hz.2)]
  apply (binaryFusionLoss_le_sum_squares hz.1 hz.2).trans
  have hu := (sq_lt_one_iff_abs_lt_one z.1).2 hz.1
  have hv := (sq_lt_one_iff_abs_lt_one z.2).2 hz.2
  linarith

theorem integral_binaryFusion_sq_eq_raw (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, |u| < 1) (hν : ∀ᵐ v ∂ν, |v| < 1) :
    (∫ z, binaryFusion z.1 z.2 ^ 2 ∂binaryFusionLaw μ ν) =
      ∫ z : ℝ × ℝ, (z.1 + z.2)^2 / (1 + z.1 * z.2) ∂μ.prod ν := by
  unfold binaryFusionLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_binaryFusion_support μ ν hμ hν] with z hz
  have hd := binaryFusion_denominator_pos hz.1 hz.2
  rw [ENNReal.toReal_ofReal hd.le, smul_eq_mul]
  unfold binaryFusion
  field_simp

theorem integral_binaryFusion_sq (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, |u| < 1) (hν : ∀ᵐ v ∂ν, |v| < 1)
    (hνsym : ν.map Neg.neg = ν) :
    (∫ z, binaryFusion z.1 z.2 ^ 2 ∂binaryFusionLaw μ ν) =
      (∫ u, u ^ 2 ∂μ) + (∫ v, v ^ 2 ∂ν) -
        ∫ z : ℝ × ℝ, binaryFusionLoss z.1 z.2 ∂μ.prod ν := by
  let F : ℝ × ℝ → ℝ := fun z => (z.1 + z.2)^2 / (1 + z.1 * z.2)
  let e : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
  have hp : MeasurePreserving e (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).prod ⟨measurable_neg, hνsym⟩
  have hsym : (∫ z : ℝ × ℝ, (z.1 - z.2)^2 / (1 - z.1 * z.2) ∂μ.prod ν) =
      ∫ z, F z ∂μ.prod ν := by
    have hh := hp.integral_comp' F
    change (∫ z : ℝ × ℝ, (z.1 + -z.2)^2 / (1 + z.1 * -z.2) ∂μ.prod ν) = _ at hh
    simpa only [mul_neg, sub_eq_add_neg] using hh
  have hF : Integrable F (μ.prod ν) := integrable_binaryFusion_integrand μ ν hμ hν
  have hFm : Integrable (fun z : ℝ × ℝ =>
      (z.1 - z.2)^2 / (1 - z.1 * z.2)) (μ.prod ν) := by
    have hh := (hp.integrable_comp hF.aestronglyMeasurable).2 hF
    change Integrable (fun z : ℝ × ℝ => (z.1 + -z.2)^2 /
      (1 + z.1 * -z.2)) (μ.prod ν) at hh
    simpa only [mul_neg, sub_eq_add_neg] using hh
  have hU : Integrable (fun z : ℝ × ℝ => z.1^2) (μ.prod ν) := by
    apply Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1
    filter_upwards [ae_binaryFusion_support μ ν hμ hν] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact ((sq_lt_one_iff_abs_lt_one z.1).2 hz.1).le
  have hV : Integrable (fun z : ℝ × ℝ => z.2^2) (μ.prod ν) := by
    apply Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1
    filter_upwards [ae_binaryFusion_support μ ν hμ hν] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact ((sq_lt_one_iff_abs_lt_one z.2).2 hz.2).le
  rw [integral_binaryFusion_sq_eq_raw μ ν hμ hν]
  change (∫ z, F z ∂μ.prod ν) = _
  calc
    (∫ z, F z ∂μ.prod ν) =
        ((∫ z, F z ∂μ.prod ν) +
          ∫ z : ℝ × ℝ, (z.1 - z.2)^2 / (1 - z.1 * z.2) ∂μ.prod ν) / 2 := by
      rw [hsym]
      ring
    _ = ∫ z : ℝ × ℝ,
        (F z + (z.1 - z.2)^2 / (1 - z.1 * z.2)) / 2 ∂μ.prod ν := by
      rw [integral_div, integral_add hF hFm]
    _ = ∫ z : ℝ × ℝ, z.1^2 + z.2^2 - binaryFusionLoss z.1 z.2 ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [ae_binaryFusion_support μ ν hμ hν] with z hz
      exact binaryFusion_symmetric_square hz.1 hz.2
    _ = _ := by
      rw [integral_sub (f := fun z : ℝ × ℝ => z.1^2 + z.2^2)
        (hU.add hV) (integrable_binaryFusionLoss_product μ ν hμ hν),
        integral_add hU hV, integral_fun_fst (fun u : ℝ => u^2),
        integral_fun_snd (fun v : ℝ => v^2)]
      simp

theorem integral_binaryFusion_sq_le_add (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, |u| < 1) (hν : ∀ᵐ v ∂ν, |v| < 1)
    (hνsym : ν.map Neg.neg = ν) :
    (∫ z, binaryFusion z.1 z.2 ^ 2 ∂binaryFusionLaw μ ν) ≤
      (∫ u, u ^ 2 ∂μ) + (∫ v, v ^ 2 ∂ν) := by
  rw [integral_binaryFusion_sq μ ν hμ hν hνsym]
  apply sub_le_self
  apply integral_nonneg_of_ae
  filter_upwards [ae_binaryFusion_support μ ν hμ hν] with z hz
  exact binaryFusionLoss_nonneg hz.1 hz.2

theorem integral_binaryFusion_sq_le_quadratic_loss (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {theta : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hμ : ∀ᵐ u ∂μ, |u| ≤ theta) (hν : ∀ᵐ v ∂ν, |v| ≤ theta)
    (hνsym : ν.map Neg.neg = ν) :
    (∫ z, binaryFusion z.1 z.2 ^ 2 ∂binaryFusionLaw μ ν) ≤
      (∫ u, u ^ 2 ∂μ) + (∫ v, v ^ 2 ∂ν) -
        2 * (1 - theta ^ 2) * (∫ u, u ^ 2 ∂μ) * (∫ v, v ^ 2 ∂ν) := by
  have hμ1 : ∀ᵐ u ∂μ, |u| < 1 := hμ.mono (fun _ h => h.trans_lt hθ1)
  have hν1 : ∀ᵐ v ∂ν, |v| < 1 := hν.mono (fun _ h => h.trans_lt hθ1)
  have hθsq : 0 ≤ 1 - theta ^ 2 := by
    have := (sq_lt_one_iff₀ hθ0).2 hθ1
    linarith
  have hfst := (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hμ
  have hsnd := (measurePreserving_snd (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hν
  have hloss : 2 * (1 - theta ^ 2) * (∫ u, u ^ 2 ∂μ) * (∫ v, v ^ 2 ∂ν) ≤
      ∫ z : ℝ × ℝ, binaryFusionLoss z.1 z.2 ∂μ.prod ν := by
    calc
      _ = ∫ z : ℝ × ℝ, 2 * (1 - theta ^ 2) * (z.1 ^ 2 * z.2 ^ 2) ∂μ.prod ν := by
        rw [integral_const_mul, integral_prod_mul (fun u : ℝ => u^2) (fun v : ℝ => v^2)]
        ring
      _ ≤ _ := by
        refine integral_mono_of_nonneg ?_ (integrable_binaryFusionLoss_product μ ν hμ1 hν1) ?_
        · exact Filter.Eventually.of_forall (fun z => by positivity)
        · filter_upwards [hfst, hsnd] with z hu hv
          simpa only [mul_assoc] using binaryFusionLoss_lower_bound hu hv hθ1
  rw [integral_binaryFusion_sq μ ν hμ1 hν1 hνsym]
  linarith

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance : Nonempty IsingSpin := ⟨.neg⟩

theorem observation_law_eq_binaryFusionLaw
    (π : Measure IsingSpin) (hπ : ∀ a, π {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, |u| < 1) (hν : ∀ᵐ v ∂ν, |v| < 1)
    (κ : Kernel IsingSpin (ℝ × ℝ))
    (hκ : ∀ a, κ a = (μ.prod ν).withDensity
      (fun z => ENNReal.ofReal ((1 + spinSign a * z.1) * (1 + spinSign a * z.2)))) :
    κ ∘ₘ π = binaryFusionLaw μ ν := by
  rw [finite_observation_law_density π (μ.prod ν) κ _ (fun _ => by fun_prop) hκ]
  unfold binaryFusionLaw
  apply withDensity_congr_ae
  filter_upwards [ae_binaryFusion_support μ ν hμ hν] with z hz
  simp only [hπ]
  exact binaryFusion_likelihood_sum hz.1.le hz.2.le

theorem integral_posterior_spinMean_sq_le_quadratic_loss
    (π : Measure IsingSpin) [IsProbabilityMeasure π]
    (hπ : ∀ a, π {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hμ : ∀ᵐ u ∂μ, |u| ≤ theta) (hν : ∀ᵐ v ∂ν, |v| ≤ theta)
    (hνsym : ν.map Neg.neg = ν)
    (κ : Kernel IsingSpin (ℝ × ℝ)) [IsFiniteKernel κ]
    (hκ : ∀ a, κ a = (μ.prod ν).withDensity
      (fun z => ENNReal.ofReal ((1 + spinSign a * z.1) * (1 + spinSign a * z.2)))) :
    (∫ z, (∫ a, spinSign a ∂(posterior κ π) z) ^ 2 ∂κ ∘ₘ π) ≤
      (∫ u, u ^ 2 ∂μ) + (∫ v, v ^ 2 ∂ν) -
        2 * (1 - theta ^ 2) * (∫ u, u ^ 2 ∂μ) * (∫ v, v ^ 2 ∂ν) := by
  have hμ1 : ∀ᵐ u ∂μ, |u| < 1 := hμ.mono (fun _ h => h.trans_lt hθ1)
  have hν1 : ∀ᵐ v ∂ν, |v| < 1 := hν.mono (fun _ h => h.trans_lt hθ1)
  have hsup := ae_binaryFusion_support μ ν hμ1 hν1
  have hpost := posterior_spinMean_eq_binaryFusion π hπ (μ.prod ν) κ
    Prod.fst Prod.snd measurable_fst measurable_snd
    (hsup.mono (fun _ h => h.1)) (hsup.mono (fun _ h => h.2)) hκ
  calc
    _ = ∫ z, binaryFusion z.1 z.2 ^ 2 ∂κ ∘ₘ π := by
      apply integral_congr_ae
      filter_upwards [hpost] with z hz
      rw [hz]
    _ = ∫ z, binaryFusion z.1 z.2 ^ 2 ∂binaryFusionLaw μ ν := by
      rw [observation_law_eq_binaryFusionLaw π hπ μ ν hμ1 hν1 κ hκ]
    _ ≤ _ := integral_binaryFusion_sq_le_quadratic_loss μ ν hθ0 hθ1 hμ hν hνsym

theorem integral_condExp_spin_sq_eq_binaryFusion
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (π : Measure IsingSpin) [IsProbabilityMeasure π]
    (hπ : ∀ a, π {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, |u| < 1) (hν : ∀ᵐ v ∂ν, |v| < 1)
    (hνsym : ν.map Neg.neg = ν)
    (κ : Kernel IsingSpin (ℝ × ℝ)) [IsFiniteKernel κ]
    (hκ : ∀ a, κ a = (μ.prod ν).withDensity
      (fun z => ENNReal.ofReal ((1 + spinSign a * z.1) * (1 + spinSign a * z.2))))
    (S : Ω → IsingSpin) (Y : Ω → ℝ × ℝ) (hS : Measurable S) (hY : Measurable Y)
    (hlaw : ρ.map (fun ω => (S ω, Y ω)) = π ⊗ₘ κ) :
    (∫ ω, (ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace (ℝ × ℝ)).comap Y] ω) ^ 2 ∂ρ) =
      (∫ u, u ^ 2 ∂μ) + (∫ v, v ^ 2 ∂ν) -
        ∫ z : ℝ × ℝ, binaryFusionLoss z.1 z.2 ∂μ.prod ν := by
  have hsup := ae_binaryFusion_support μ ν hμ hν
  have hpost := condExp_spin_eq_binaryFusion_of_likelihood ρ π hπ (μ.prod ν) κ
    S Y hS hY hlaw Prod.fst Prod.snd measurable_fst measurable_snd
    (hsup.mono (fun _ h => h.1)) (hsup.mono (fun _ h => h.2)) hκ
  have hYlaw : ρ.map Y = binaryFusionLaw μ ν := by
    rw [← Measure.snd_map_prodMk hS hY, hlaw, Measure.snd_compProd]
    exact observation_law_eq_binaryFusionLaw π hπ μ ν hμ hν κ hκ
  have hm : Measurable (fun z : ℝ × ℝ => binaryFusion z.1 z.2 ^ 2) := by
    unfold binaryFusion
    fun_prop
  calc
    _ = ∫ ω, binaryFusion (Y ω).1 (Y ω).2 ^ 2 ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hpost] with ω hω
      rw [hω]
    _ = ∫ z, binaryFusion z.1 z.2 ^ 2 ∂binaryFusionLaw μ ν := by
      rw [← hYlaw]
      exact (integral_map hY.aemeasurable hm.aestronglyMeasurable).symm
    _ = _ := integral_binaryFusion_sq μ ν hμ hν hνsym

theorem integral_condExp_spin_sq_le_quadratic_loss
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (π : Measure IsingSpin) [IsProbabilityMeasure π]
    (hπ : ∀ a, π {a} = ENNReal.ofReal (1 / 2 : ℝ))
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hμ : ∀ᵐ u ∂μ, |u| ≤ theta) (hν : ∀ᵐ v ∂ν, |v| ≤ theta)
    (hνsym : ν.map Neg.neg = ν)
    (κ : Kernel IsingSpin (ℝ × ℝ)) [IsFiniteKernel κ]
    (hκ : ∀ a, κ a = (μ.prod ν).withDensity
      (fun z => ENNReal.ofReal ((1 + spinSign a * z.1) * (1 + spinSign a * z.2))))
    (S : Ω → IsingSpin) (Y : Ω → ℝ × ℝ) (hS : Measurable S) (hY : Measurable Y)
    (hlaw : ρ.map (fun ω => (S ω, Y ω)) = π ⊗ₘ κ) :
    (∫ ω, (ρ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace (ℝ × ℝ)).comap Y] ω) ^ 2 ∂ρ) ≤
      (∫ u, u ^ 2 ∂μ) + (∫ v, v ^ 2 ∂ν) -
        2 * (1 - theta ^ 2) * (∫ u, u ^ 2 ∂μ) * (∫ v, v ^ 2 ∂ν) := by
  have hμ1 : ∀ᵐ u ∂μ, |u| < 1 := hμ.mono (fun _ h => h.trans_lt hθ1)
  have hν1 : ∀ᵐ v ∂ν, |v| < 1 := hν.mono (fun _ h => h.trans_lt hθ1)
  rw [integral_condExp_spin_sq_eq_binaryFusion ρ π hπ μ ν hμ1 hν1 hνsym
    κ hκ S Y hS hY hlaw,
    ← integral_binaryFusion_sq μ ν hμ1 hν1 hνsym]
  exact integral_binaryFusion_sq_le_quadratic_loss μ ν hθ0 hθ1 hμ hν hνsym

end Problem367

end

end OAI
