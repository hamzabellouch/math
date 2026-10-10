import OAI.Probability.FreeIsing.Conditioning.FiniteBayesExp

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Problem367.FiniteBayes

variable {S X : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S] [Nonempty S] [MeasurableSpace X]

theorem condExp_state_eq_posterior_integral (π : Measure S) [IsFiniteMeasure π]
    (κ : Kernel S X) [IsFiniteKernel κ] (A : S → ℝ) :
    (π ⊗ₘ κ)[fun z : S × X => A z.1 | (inferInstance : MeasurableSpace X).comap Prod.snd]
      =ᵐ[π ⊗ₘ κ] fun z => ∫ s, A s ∂(κ†π) z.2 := by
  have hint : Integrable (fun z : S × X => A z.1) (π ⊗ₘ κ) := by
    apply (integrable_const (∑ s, |A s|)).mono'
    · exact ((measurable_of_finite A).comp measurable_fst).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun s _ => abs_nonneg (A s)) (Finset.mem_univ z.1)
  have hcd : condDistrib (Prod.fst : S × X → S) Prod.snd (π ⊗ₘ κ) = κ†π := by
    rw [condDistrib, posterior]
    rfl
  have hc := condExp_ae_eq_integral_condDistrib
    (μ := π ⊗ₘ κ) (X := Prod.snd) (Y := Prod.fst)
    measurable_snd measurable_fst.aemeasurable (measurable_of_finite A).stronglyMeasurable hint
  rwa [hcd] at hc

theorem condExp_state_eq_real_likelihood (π : Measure S) [IsProbabilityMeasure π]
    (ν : Measure X) [SigmaFinite ν] (κ : Kernel S X) [IsFiniteKernel κ]
    {L : S → X → ℝ} (hL : ∀ s, Measurable (L s)) (hLpos : ∀ s x, 0 < L s x)
    (hκ : ∀ s, κ s = ν.withDensity (fun x => ENNReal.ofReal (L s x))) (A : S → ℝ) :
    (π ⊗ₘ κ)[fun z : S × X => A z.1 | (inferInstance : MeasurableSpace X).comap Prod.snd]
      =ᵐ[π ⊗ₘ κ] fun z =>
        (∑ s, π.real {s} * L s z.2 * A s) / (∑ s, π.real {s} * L s z.2) := by
  apply (condExp_state_eq_posterior_integral π κ A).trans
  have hp := posterior_integral π κ ν L hL hLpos hκ A
  rw [← Measure.snd_compProd π κ] at hp
  exact ae_of_ae_map measurable_snd.aemeasurable hp

theorem condExp_state_eq_exponential_likelihood (π : Measure S) [IsProbabilityMeasure π]
    (ν : Measure X) [SigmaFinite ν] (κ : Kernel S X) [IsFiniteKernel κ]
    (E : S → X → ℝ) (hE : ∀ s, Measurable (E s))
    (c : X → ℝ) (hc : Measurable c) (hcpos : ∀ x, 0 < c x)
    (hκ : ∀ s, κ s = ν.withDensity (fun x => ENNReal.ofReal (c x * Real.exp (E s x))))
    (A : S → ℝ) :
    (π ⊗ₘ κ)[fun z : S × X => A z.1 | (inferInstance : MeasurableSpace X).comap Prod.snd]
      =ᵐ[π ⊗ₘ κ] fun z =>
        (∑ s, π.real {s} * Real.exp (E s z.2) * A s) /
          (∑ s, π.real {s} * Real.exp (E s z.2)) := by
  apply (condExp_state_eq_posterior_integral π κ A).trans
  have hp := posterior_integral_exp π κ ν E hE c hc hcpos hκ A
  rw [← Measure.snd_compProd π κ] at hp
  exact ae_of_ae_map measurable_snd.aemeasurable hp

section OriginalSpace

variable {Ω : Type*} [MeasurableSpace Ω]

omit [Fintype S] [MeasurableSingletonClass S] in

theorem condDistrib_eq_posterior_of_joint_law
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure S) [IsFiniteMeasure π]
    (κ : Kernel S X) [IsFiniteKernel κ] (Z : Ω → S) (Y : Ω → X)
    (hZ : Measurable Z) (hY : Measurable Y)
    (hlaw : μ.map (fun ω => (Z ω, Y ω)) = π ⊗ₘ κ) :
    condDistrib Z Y μ = κ†π := by
  rw [condDistrib, posterior]
  congr 1
  rw [← hlaw, Measure.map_map measurable_swap (hZ.prodMk hY)]
  rfl

theorem condExp_state_eq_posterior_integral_of_joint_law
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure S) [IsFiniteMeasure π]
    (κ : Kernel S X) [IsFiniteKernel κ] (Z : Ω → S) (Y : Ω → X)
    (hZ : Measurable Z) (hY : Measurable Y)
    (hlaw : μ.map (fun ω => (Z ω, Y ω)) = π ⊗ₘ κ) (A : S → ℝ) :
    μ[fun ω => A (Z ω) | (inferInstance : MeasurableSpace X).comap Y]
      =ᵐ[μ] fun ω => ∫ s, A s ∂(κ†π) (Y ω) := by
  have hint : Integrable (fun ω => A (Z ω)) μ := by
    apply (integrable_const (∑ s, |A s|)).mono'
    · exact ((measurable_of_finite A).comp hZ).aestronglyMeasurable
    · filter_upwards [] with ω
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun s _ => abs_nonneg (A s)) (Finset.mem_univ (Z ω))
  have hc := condExp_ae_eq_integral_condDistrib hY hZ.aemeasurable
    (measurable_of_finite A).stronglyMeasurable hint
  rwa [condDistrib_eq_posterior_of_joint_law μ π κ Z Y hZ hY hlaw] at hc

theorem condExp_state_eq_of_posterior_integral
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure S) [IsFiniteMeasure π]
    (κ : Kernel S X) [IsFiniteKernel κ] (Z : Ω → S) (Y : Ω → X)
    (hZ : Measurable Z) (hY : Measurable Y)
    (hlaw : μ.map (fun ω => (Z ω, Y ω)) = π ⊗ₘ κ)
    (A : S → ℝ) (g : X → ℝ)
    (hpost : (fun x => ∫ s, A s ∂(κ†π) x) =ᵐ[κ ∘ₘ π] g) :
    μ[fun ω => A (Z ω) | (inferInstance : MeasurableSpace X).comap Y]
      =ᵐ[μ] fun ω => g (Y ω) := by
  apply (condExp_state_eq_posterior_integral_of_joint_law μ π κ Z Y hZ hY hlaw A).trans
  have hYlaw : μ.map Y = κ ∘ₘ π := by
    rw [← Measure.snd_map_prodMk hZ hY, hlaw, Measure.snd_compProd]
  rw [← hYlaw] at hpost
  exact ae_of_ae_map hY.aemeasurable hpost

end OriginalSpace

end Problem367.FiniteBayes

end

end OAI
