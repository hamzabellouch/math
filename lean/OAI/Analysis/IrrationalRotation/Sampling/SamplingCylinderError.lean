import OAI.Analysis.IrrationalRotation.Sampling.SamplingCylinderWeak
import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.SamplingCylinderWeak
open ProductModel

theorem weaklyConverges_of_real_cylinders
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hη : ∀ n, IsFiniteMeasure (η n)) (hν : IsFiniteMeasure ν)
    (h : ∀ t : CylinderTest (Bool × ℕ),
      Tendsto (fun n => (η n).real (endpointCylinder t)) atTop
        (𝓝 (ν.real (endpointCylinder t)))) :
    WeaklyConverges η ν := by
  apply weaklyConverges_of_cylinders hη hν
  intro t
  exact (ENNReal.tendsto_toReal_iff
    (fun n => by let := hη n; exact measure_ne_top _ _)
    (by let := hν; exact measure_ne_top _ _)).mp (h t)

theorem abs_integral_sub_le_eLpNorm_two
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤
      (eLpNorm (fun x => f x - g x) 2 μ).toReal := by
  have hd : MemLp (fun x => f x - g x) 2 μ := hf.sub hg
  rw [← integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num)),
    ← Real.norm_eq_abs]
  calc
    ‖∫ x, f x - g x ∂μ‖ ≤ ∫ x, ‖f x - g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = (eLpNorm (fun x => f x - g x) 1 μ).toReal := by
      rw [integral_norm_eq_lintegral_enorm hd.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm hd.aestronglyMeasurable]
    _ ≤ (eLpNorm (fun x => f x - g x) 2 μ).toReal :=
      ENNReal.toReal_mono hd.eLpNorm_ne_top
        (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

theorem tendsto_integral_of_eLpNorm_sub_tendsto_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f g : ℕ → X → ℝ} {a : ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (herror : Tendsto (fun n => eLpNorm (fun x => f n x - g n x) 2 μ) atTop (𝓝 0))
    (hideal : Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 a)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 a) := by
  have hnorm : Tendsto (fun n => (eLpNorm (fun x => f n x - g n x) 2 μ).toReal)
      atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herror
  have hdiff : Tendsto (fun n => (∫ x, f n x ∂μ) - ∫ x, g n x ∂μ)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hnorm
    intro n
    simpa only [Real.norm_eq_abs] using abs_integral_sub_le_eLpNorm_two (hf n) (hg n)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hideal

theorem real_mass_eq_integral_of_tested_first_marginal
    {η : Measure EndpointPair} {R : Set EndpointPair}
    {f : Base → ℝ} (hf : MemLp f 2 baseMeasure) (hf0 : 0 ≤ᵐ[baseMeasure] f)
    (hmarginal : (η.restrict R).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f x))) :
    η.real R = ∫ x, f x ∂baseMeasure := by
  have hmass := congrArg (fun ν : Measure Base => ν univ) hmarginal
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  rw [Measure.real, hmass]
  exact (integral_eq_lintegral_of_nonneg_ae hf0 hf.aestronglyMeasurable).symm

theorem weaklyConverges_of_tested_first_marginal_L2
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hη : ∀ n, IsFiniteMeasure (η n)) (hν : IsFiniteMeasure ν)
    (f g : CylinderTest (Bool × ℕ) → ℕ → Base → ℝ)
    (hf : ∀ t n, MemLp (f t n) 2 baseMeasure)
    (hg : ∀ t n, MemLp (g t n) 2 baseMeasure)
    (hf0 : ∀ t n, 0 ≤ᵐ[baseMeasure] f t n)
    (hmarginal : ∀ t n, ((η n).restrict (endpointCylinder t)).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f t n x)))
    (herror : ∀ t, Tendsto
      (fun n => eLpNorm (fun x => f t n x - g t n x) 2 baseMeasure) atTop (𝓝 0))
    (hideal : ∀ t, Tendsto (fun n => ∫ x, g t n x ∂baseMeasure) atTop
      (𝓝 (ν.real (endpointCylinder t)))) :
    WeaklyConverges η ν := by
  apply weaklyConverges_of_real_cylinders hη hν
  intro t
  have heq (n : ℕ) := real_mass_eq_integral_of_tested_first_marginal
    (hf t n) (hf0 t n) (hmarginal t n)
  simpa only [heq] using tendsto_integral_of_eLpNorm_sub_tendsto_zero
    (hf t) (hg t) (herror t) (hideal t)

theorem ae_all_triangular_weaklyConverges_of_tested_L2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (η : Finset ℕ → Ω → ℕ → Measure EndpointPair)
    (hη : ∀ I ω n, IsFiniteMeasure (η I ω n))
    (f : Finset ℕ → CylinderTest (Bool × ℕ) → Ω → ℕ → Base → ℝ)
    (g : Finset ℕ → CylinderTest (Bool × ℕ) → ℕ → Base → ℝ)
    (hf : ∀ I t ω n, MemLp (f I t ω n) 2 baseMeasure)
    (hg : ∀ I t n, MemLp (g I t n) 2 baseMeasure)
    (hf0 : ∀ I t ω n, 0 ≤ᵐ[baseMeasure] f I t ω n)
    (hmarginal : ∀ I t ω n, ((η I ω n).restrict (endpointCylinder t)).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f I t ω n x)))
    (herror : ∀ I t, ∀ᵐ ω ∂P, Tendsto
      (fun n => eLpNorm (fun x => f I t ω n x - g I t n x) 2 baseMeasure)
      atTop (𝓝 0))
    (hideal : ∀ I t, Tendsto (fun n => ∫ x, g I t n x ∂baseMeasure) atTop
      (𝓝 ((triangularLaw I).real (endpointCylinder t)))) :
    ∀ᵐ ω ∂P, ∀ I, WeaklyConverges (η I ω) (triangularLaw I) := by
  have hall : ∀ᵐ ω ∂P, ∀ I t, Tendsto
      (fun n => eLpNorm (fun x => f I t ω n x - g I t n x) 2 baseMeasure)
      atTop (𝓝 0) := ae_all_iff.mpr fun I => ae_all_iff.mpr (herror I)
  filter_upwards [hall] with ω hω
  intro I
  have hν : IsFiniteMeasure (triangularLaw I) := by unfold triangularLaw; infer_instance
  exact weaklyConverges_of_tested_first_marginal_L2 (hη I ω) hν
    (fun t => f I t ω) (g I) (fun t => hf I t ω) (hg I)
    (fun t => hf0 I t ω) (fun t => hmarginal I t ω) (hω I) (hideal I)

end Invariant233.SamplingCylinderWeak

end

end OAI
