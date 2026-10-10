import OAI.Probability.FreeIsing.Gaussian.FiniteGaussianPlanted
import OAI.Probability.FreeIsing.Posterior.Fields

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

theorem gaussianPi_map_sqrt {I : Type*} [Fintype I]
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : I => gaussianReal 0 1)).map
      (fun x i => Real.sqrt t * x i) =
        Measure.pi (fun _ : I => gaussianReal 0 ⟨t, ht⟩) := by
  rw [Measure.pi_map_pi (μ := fun _ : I => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => Real.sqrt t * x) (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    change (Real.sqrt t) ^ 2 * 1 = t
    rw [mul_one, Real.sq_sqrt ht]

theorem finiteStandardGaussianPlanted_joint_law
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype I] (μ : Measure S) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ) :
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))).map
      (fun z : S × (I → ℝ) =>
        (z.1, fun i => t * spin z.1 i + Real.sqrt t * z.2 i)) =
      μ ⊗ₘ finiteGaussianObservationKernel ⟨t, ht⟩ spin := by
  have : IsMarkovKernel (finiteGaussianObservationKernel ⟨t, ht⟩ spin) :=
    finiteGaussianObservationKernel_isMarkov ⟨t, ht⟩ spin
  apply map_planted_eq_compProd μ (Measure.pi (fun _ : I => gaussianReal 0 1))
    (finiteGaussianObservationKernel ⟨t, ht⟩ spin)
    (fun s x i => t * spin s i + Real.sqrt t * x i)
  · exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd)))
  · intro s
    have hscale : Measurable (fun x : I → ℝ => fun i => Real.sqrt t * x i) := by
      fun_prop
    have hshift : Measurable (fun x : I → ℝ => fun i => t * spin s i + x i) := by
      fun_prop
    rw [show (fun x : I → ℝ => fun i => t * spin s i + Real.sqrt t * x i) =
      (fun x : I → ℝ => fun i => t * spin s i + x i) ∘
        (fun x : I → ℝ => fun i => Real.sqrt t * x i) from rfl,
      ← Measure.map_map hshift hscale, gaussianPi_map_sqrt t ht]
    exact gaussianPi_map_signal ⟨t, ht⟩ (spin s)

namespace FinitePosterior

theorem exponential_posterior_eq_fieldMean
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    [MeasurableSpace S] (μ : Measure S) (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → I → ℝ) (q : S → ℝ) (x : I → ℝ) :
    (∑ s, μ.real {s} * Real.exp (∑ i, spin s i * x i) * q s) /
      (∑ s, μ.real {s} * Real.exp (∑ i, spin s i * x i)) =
      fieldMean energy spin q x := by
  let Z := ∑ s, Real.exp (energy s)
  have hZ : Z ≠ 0 := ne_of_gt (Finset.sum_pos
    (fun s _ => Real.exp_pos (energy s)) Finset.univ_nonempty)
  have hw (s : S) :
      μ.real {s} * Real.exp (∑ i, spin s i * x i) =
        Real.exp (fieldEnergy energy spin x s) / Z := by
    rw [hprior s]
    have hsum : (∑ i, spin s i * x i) = ∑ i, x i * spin s i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    simp only [fieldEnergy, Real.exp_add, Z]
    ring
  simp_rw [hw, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hZ]
  unfold fieldMean
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

end FinitePosterior

theorem finiteStandardGaussianPlanted_condExp_fieldMean
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [StandardBorelSpace S] [Nonempty S] [Fintype I]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ)
    (hspin : ∀ s i, spin s i ^ 2 = 1) (q : S → ℝ) :
    let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
    let Y : S × (I → ℝ) → I → ℝ :=
      fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
    ρ[fun z => q z.1 | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] =ᵐ[ρ]
      fun z => FinitePosterior.fieldMean energy spin q (Y z) := by
  dsimp only
  have : IsMarkovKernel (finiteGaussianObservationKernel ⟨t, ht⟩ spin) :=
    finiteGaussianObservationKernel_isMarkov ⟨t, ht⟩ spin
  apply FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))) μ
    (finiteGaussianObservationKernel ⟨t, ht⟩ spin) Prod.fst
    (fun z i => t * spin z.1 i + Real.sqrt t * z.2 i) measurable_fst
    (by exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd))))
    (finiteStandardGaussianPlanted_joint_law μ t ht spin) q
  filter_upwards [finiteGaussianObservation_posterior_mean μ ⟨t, ht⟩ spin hspin q]
    with x hx
  exact hx.trans (FinitePosterior.exponential_posterior_eq_fieldMean
    μ energy hprior spin q x)

theorem finiteStandardGaussianPlanted_integral_test_fieldMean
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [StandardBorelSpace S] [Nonempty S] [Fintype I]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ)
    (hspin : ∀ s i, spin s i ^ 2 = 1) (q : S → ℝ)
    (h : (I → ℝ) → ℝ) (hh : Measurable h) (C : ℝ)
    (hbound : ∀ x, ‖h x‖ ≤ C) :
    let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
    let Y : S × (I → ℝ) → I → ℝ :=
      fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
    (∫ z, h (Y z) * q z.1 ∂ρ) =
      ∫ z, h (Y z) * FinitePosterior.fieldMean energy spin q (Y z) ∂ρ := by
  let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
  let Y : S × (I → ℝ) → I → ℝ :=
    fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
  change (∫ z, h (Y z) * q z.1 ∂ρ) = _
  have hY : Measurable Y := by
    exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd)))
  have hm : (inferInstance : MeasurableSpace (I → ℝ)).comap Y ≤
      (inferInstance : MeasurableSpace (S × (I → ℝ))) := hY.comap_le
  have htest : StronglyMeasurable[(inferInstance : MeasurableSpace (I → ℝ)).comap Y]
      (fun z => h (Y z)) :=
    (hh.comp (comap_measurable Y)).stronglyMeasurable
  have hq : Integrable (fun z : S × (I → ℝ) => q z.1) ρ := by
    apply (integrable_const (∑ s, |q s|)).mono'
    · exact ((measurable_of_finite q).comp measurable_fst).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun s _ => abs_nonneg (q s)) (Finset.mem_univ z.1)
  have hpull := condExp_stronglyMeasurable_mul_of_bound hm htest hq C
    (Filter.Eventually.of_forall (fun z => hbound (Y z)))
  have hposterior := finiteStandardGaussianPlanted_condExp_fieldMean
    μ energy hprior t ht spin hspin q
  calc
    (∫ z, h (Y z) * q z.1 ∂ρ) =
        ∫ z, ρ[(fun z => h (Y z)) * (fun z => q z.1) | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] z ∂ρ :=
      (integral_condExp hm).symm
    _ = ∫ z, h (Y z) * ρ[(fun z => q z.1) | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] z ∂ρ :=
      integral_congr_ae hpull
    _ = ∫ z, h (Y z) * FinitePosterior.fieldMean energy spin q (Y z) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hposterior] with z hz
      rw [hz]

end Problem367

end

end OAI
