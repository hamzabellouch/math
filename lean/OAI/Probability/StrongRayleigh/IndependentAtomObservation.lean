import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem336AdditiveD139.IndependentAtomObservation

variable {Ω : Type u_1} {F : Type u_2} {E : Type u_3} {Y : Type u_4} [MeasurableSpace Ω] [MeasurableSpace F]
    [MeasurableSpace E] [MeasurableSpace Y] [MeasurableSingletonClass F]
    {μ : Measure Ω} {X : Ω → F} {Z : Ω → E}

theorem map_noise_restrict_atom (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (x : F) :
    Measure.map Z (μ.restrict (X ⁻¹' {x})) =
      μ (X ⁻¹' {x}) • Measure.map Z μ := by
  ext s hs
  rw [Measure.map_apply hZ hs, Measure.restrict_apply (hZ hs),
    Measure.smul_apply, smul_eq_mul, Measure.map_apply hZ hs]
  rw [Set.inter_comm]
  exact hind.measure_inter_preimage_eq_mul {x} s (measurableSet_singleton x) hs

theorem map_observation_restrict_atom (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (T : F → E → Y) (x : F) (hT : Measurable (T x)) :
    Measure.map (fun ω => T (X ω) (Z ω)) (μ.restrict (X ⁻¹' {x})) =
      μ (X ⁻¹' {x}) • Measure.map (T x) (Measure.map Z μ) := by
  have heq : (fun ω => T (X ω) (Z ω)) =ᵐ[μ.restrict (X ⁻¹' {x})]
      (fun ω => T x (Z ω)) := by
    filter_upwards [ae_restrict_mem (hX (measurableSet_singleton x))] with ω hω
    have hx : X ω = x := hω
    rw [hx]
  rw [Measure.map_congr heq]
  change Measure.map (T x ∘ Z) (μ.restrict (X ⁻¹' {x})) = _
  rw [← Measure.map_map hT hZ, map_noise_restrict_atom hZ hind x, Measure.map_smul _ hT.aemeasurable]

theorem map_observation_restrict_atom_of_hasLaw (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) {ρ : Measure E} (hρ : HasLaw Z ρ μ)
    (T : F → E → Y) (x : F) (hT : Measurable (T x)) :
    Measure.map (fun ω => T (X ω) (Z ω)) (μ.restrict (X ⁻¹' {x})) =
      μ (X ⁻¹' {x}) • Measure.map (T x) ρ := by
  rw [map_observation_restrict_atom hX hZ hind T x hT, hρ.map_eq]

theorem map_observation_restrict_atom_withDensity (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) {ρ : Measure E} (hρ : HasLaw Z ρ μ)
    (T : F → E → Y) (x : F) (hT : Measurable (T x))
    (ν : Measure Y) (L : Y → ℝ≥0∞) (hL : Measurable L)
    (hlaw : Measure.map (T x) ρ = ν.withDensity L) :
    Measure.map (fun ω => T (X ω) (Z ω)) (μ.restrict (X ⁻¹' {x})) =
      ν.withDensity (fun y => μ (X ⁻¹' {x}) * L y) := by
  rw [map_observation_restrict_atom_of_hasLaw hX hZ hind hρ T x hT, hlaw]
  exact (withDensity_smul (μ (X ⁻¹' {x})) hL).symm

theorem map_observation_restrict_atom_withDensity_ofReal [IsFiniteMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hind : IndepFun X Z μ)
    {ρ : Measure E} (hρ : HasLaw Z ρ μ)
    (T : F → E → Y) (x : F) (hT : Measurable (T x))
    (ν : Measure Y) (L : Y → ℝ) (hL : Measurable L)
    (hlaw : Measure.map (T x) ρ = ν.withDensity (fun y => ENNReal.ofReal (L y))) :
    Measure.map (fun ω => T (X ω) (Z ω)) (μ.restrict (X ⁻¹' {x})) =
      ν.withDensity (fun y => ENNReal.ofReal ((μ (X ⁻¹' {x})).toReal * L y)) := by
  rw [map_observation_restrict_atom_withDensity hX hZ hind hρ T x hT ν
    (fun y => ENNReal.ofReal (L y)) hL.ennreal_ofReal hlaw]
  congr 1
  funext y
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end Problem336AdditiveD139.IndependentAtomObservation

end

end OAI
