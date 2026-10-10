import Mathlib
import OAI.Probability.SKGap.Localization.KernelDensity

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
lemma integrable_bounded (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f μ := Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)

theorem continuous_kernel_posterior (μ ρ : Measure (ι → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {φ p : (κ → ℝ) → ℝ} (hφ : Continuous φ) (hp : Continuous p)
    (hφpos : ∀ y,0 ≤ φ y) (hppos : ∀ y,0 ≤ p y)
    {C : ℝ} (hC : 0 ≤ C) (hφC : ∀ y,φ y ≤ C)
    {L : (ι → ℝ) → (κ → ℝ)} {K : (κ → ℝ) → (ι → ℝ)}
    (hL : Continuous L) (hK : Continuous K)
    (hjoint : (μ.prod ((volume : Measure (κ → ℝ)).withDensity (fun y => ENNReal.ofReal (φ y)))).map
      (fun z => (z.1,L z.1+z.2)) =
      (ρ.prod ((volume : Measure (κ → ℝ)).withDensity (fun y => ENNReal.ofReal (p y)))).map
        (fun z => (z.1+K z.2,z.2))) (z : κ → ℝ) :
    μ.withDensity (fun x => ENNReal.ofReal (φ (z-L x))) =
      ENNReal.ofReal (p z) • ρ.map (fun r => r+K z) := by
  have hiφ (y : κ → ℝ) : Integrable (fun x => φ (y-L x)) μ :=
    integrable_bounded μ (by fun_prop) (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
  have := isFiniteMeasure_withDensity_ofReal (hiφ z).hasFiniteIntegral
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  let fr : (ι → ℝ) →ᵇ ℝ := ⟨⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩,
    f.map_bounded'⟩
  have hfr (x : ι → ℝ) : 0 ≤ fr x := (f x).coe_nonneg
  have hb (x : ι → ℝ) : ‖fr x‖ ≤ ‖fr‖ := fr.norm_coe_le_norm x
  have hi1 (y : κ → ℝ) : Integrable (fun x => φ (y-L x)*fr x) μ := by
    apply integrable_bounded μ (by fun_prop) (C := C*‖fr‖)
    intro x
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφpos _)]
    exact mul_le_mul (hφC _) (hb x) (norm_nonneg _) hC
  have hi2 (y : κ → ℝ) : Integrable (fun r => fr (r+K y)) ρ :=
    integrable_bounded ρ (by fun_prop) (fun r => hb _)
  have hc1 : Continuous (fun y => ∫ x, φ (y-L x)*fr x ∂μ) := by
    apply continuous_of_dominated (bound := fun _ => C*‖fr‖)
    · intro y; exact (hi1 y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun x => by
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφpos _)]
        exact mul_le_mul (hφC _) (hb x) (norm_nonneg _) hC)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall (fun x => by fun_prop)
  have hc2 : Continuous (fun y => ∫ r, fr (r+K y) ∂ρ) := by
    apply continuous_of_dominated (bound := fun _ => ‖fr‖)
    · intro y; exact (hi2 y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun r => hb _)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall (fun r => by fun_prop)
  have he1 (y : κ → ℝ) :
      (∫⁻ x, ENNReal.ofReal (φ (y-L x))*(f x : ℝ≥0∞) ∂μ)=
      ENNReal.ofReal (∫ x, φ (y-L x)*fr x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi1 y) (Filter.Eventually.of_forall (fun x => mul_nonneg (hφpos _) (hfr x)))]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (hφpos _)]
    change _ * (f x : ℝ≥0∞) = _ * ENNReal.ofReal (f x : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
  have he2 (y : κ → ℝ) :
      ENNReal.ofReal (p y)*(∫⁻ r, (f (r+K y) : ℝ≥0∞) ∂ρ)=
      ENNReal.ofReal (p y*(∫ r, fr (r+K y) ∂ρ)) := by
    rw [ENNReal.ofReal_mul (hppos y),ofReal_integral_eq_lintegral_ofReal (hi2 y)
      (Filter.Eventually.of_forall (fun r => hfr _))]
    congr 1
    apply lintegral_congr
    intro r
    change (f (r+K y) : ℝ≥0∞) = ENNReal.ofReal (f (r+K y) : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
  have hae := kernel_test_ae μ ρ hφ.measurable.ennreal_ofReal hp.measurable.ennreal_ofReal
    hL.measurable hK.measurable hjoint (fun x => (f x : ℝ≥0∞)) (by fun_prop)
  simp only [he1,he2] at hae
  have hall := (Continuous.ae_eq_iff_eq (volume : Measure (κ → ℝ))
    (ENNReal.continuous_ofReal.comp hc1) (ENNReal.continuous_ofReal.comp (hp.mul hc2))).mp hae
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_smul_measure,lintegral_map (by fun_prop) (by fun_prop)]
  change (∫⁻ x, ENNReal.ofReal (φ (z-L x))*(f x : ℝ≥0∞) ∂μ)=
    ENNReal.ofReal (p z)*(∫⁻ r, (f (r+K z) : ℝ≥0∞) ∂ρ)
  rw [he1,he2]
  exact congrFun hall z

end SKGap.GaussianDensity
end
end

end OAI
