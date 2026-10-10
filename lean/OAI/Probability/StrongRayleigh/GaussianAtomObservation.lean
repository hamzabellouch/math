import OAI.Probability.StrongRayleigh.GaussianObservation
import OAI.Probability.StrongRayleigh.IndependentAtomLaw

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem336AdditiveD139.GaussianAtomObservation

theorem gaussian_pi_map_binary_shift {F : Type u_1} [Fintype F]
    (t : ℝ≥0) (ht : t ≠ 0) (x : F → Bool) :
    (Measure.pi (fun _ : F => gaussianReal 0 t)).map
      (fun b i => (t : ℝ) * boolReal (x i) + b i) =
      (Measure.pi (fun _ : F => gaussianReal 0 t)).withDensity
        (fun y => ENNReal.ofReal (GaussianObservation.likelihood t x y)) := by
  rw [Measure.pi_map_pi (f := fun i b => (t : ℝ) * boolReal (x i) + b)
    (fun i => (measurable_const.add measurable_id).aemeasurable)]
  simp_rw [gaussianReal_map_const_add, zero_add]
  exact GaussianObservation.gaussianReal_pi_binary_shift t ht x

theorem gaussian_observation_atom_density
    {Ω : Type u_2} {A : Type u_3} {F : Type u_4} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype F]
    {μ : Measure Ω} {X : Ω → A} {B : Ω → F → ℝ}
    (hX : Measurable X) (hBm : Measurable B) (t : ℝ≥0) (ht : t ≠ 0)
    (hB : HasLaw B (Measure.pi (fun _ : F => gaussianReal 0 t)) μ)
    (hind : IndepFun X B μ) (q : A → F → Bool)
    (x : A) :
    (μ.restrict (X ⁻¹' {x})).map
        (fun ω i => (t : ℝ) * boolReal (q (X ω) i) + B ω i) =
      (Measure.pi (fun _ : F => gaussianReal 0 t)).withDensity
        (fun y => μ (X ⁻¹' {x}) * ENNReal.ofReal
          (GaussianObservation.likelihood t (q x) y)) := by
  exact IndependentAtomLaw.map_observation_restrict_atom_withDensity
    (H := fun x b i => (t : ℝ) * boolReal (q x i) + b i)
    hX hBm hind hB.map_eq x (by fun_prop)
    (GaussianObservation.measurable_likelihood t (q x)).ennreal_ofReal
    (gaussian_pi_map_binary_shift t ht (q x))

theorem gaussian_observation_atom_density_real
    {Ω : Type u_5} {A : Type u_6} {F : Type u_7} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype F]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → A} {B : Ω → F → ℝ}
    (hX : Measurable X) (hBm : Measurable B) (t : ℝ≥0) (ht : t ≠ 0)
    (hB : HasLaw B (Measure.pi (fun _ : F => gaussianReal 0 t)) μ)
    (hind : IndepFun X B μ) (q : A → F → Bool)
    (x : A) :
    (μ.restrict (X ⁻¹' {x})).map
        (fun ω i => (t : ℝ) * boolReal (q (X ω) i) + B ω i) =
      (Measure.pi (fun _ : F => gaussianReal 0 t)).withDensity
        (fun y => ENNReal.ofReal ((μ (X ⁻¹' {x})).toReal *
          GaussianObservation.likelihood t (q x) y)) := by
  rw [gaussian_observation_atom_density hX hBm t ht hB hind q x]
  congr 1
  funext y
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top μ _)]

end Problem336AdditiveD139.GaussianAtomObservation

end

end OAI
