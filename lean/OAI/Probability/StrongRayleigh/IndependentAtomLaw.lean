import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Problem336AdditiveD139.IndependentAtomLaw

variable {Ω : Type u_1} {α : Type u_2} {β : Type u_3} {γ : Type u_4} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω}

theorem map_restrict_of_indep {X : Ω → α} {N : Ω → β}
    (hN : Measurable N) (hi : IndepFun X N μ)
    {s : Set α} (hs : MeasurableSet s) :
    Measure.map N (μ.restrict (X ⁻¹' s)) = μ (X ⁻¹' s) • Measure.map N μ := by
  ext t ht
  rw [Measure.map_apply hN ht, Measure.restrict_apply (hN ht),
    Measure.smul_apply, Measure.map_apply hN ht]
  rw [inter_comm]
  exact hi.measure_inter_preimage_eq_mul s t hs ht

theorem map_observation_restrict_atom [MeasurableSingletonClass α]
    {X : Ω → α} {N : Ω → β} {H : α → β → γ}
    (hX : Measurable X) (hN : Measurable N) (hi : IndepFun X N μ)
    (x : α) (hH : Measurable (H x)) :
    Measure.map (fun ω => H (X ω) (N ω)) (μ.restrict (X ⁻¹' {x})) =
      μ (X ⁻¹' {x}) • Measure.map (H x) (Measure.map N μ) := by
  have heq : (fun ω => H (X ω) (N ω)) =ᵐ[μ.restrict (X ⁻¹' {x})]
      (fun ω => H x (N ω)) := by
    filter_upwards [ae_restrict_mem (hX (measurableSet_singleton x))] with ω hω
    have hx : X ω = x := hω
    rw [hx]
  rw [Measure.map_congr heq]
  change Measure.map (H x ∘ N) (μ.restrict (X ⁻¹' {x})) = _
  rw [← Measure.map_map hH hN,
    map_restrict_of_indep hN hi (measurableSet_singleton x), Measure.map_smul _ hH.aemeasurable]

theorem map_observation_restrict_atom_withDensity [MeasurableSingletonClass α]
    {X : Ω → α} {N : Ω → β} {H : α → β → γ} {ν : Measure β} {ρ : Measure γ}
    (hX : Measurable X) (hN : Measurable N) (hi : IndepFun X N μ)
    (hNlaw : Measure.map N μ = ν) (x : α) (hH : Measurable (H x))
    {L : γ → ℝ≥0∞} (hL : Measurable L)
    (hDensity : Measure.map (H x) ν = ρ.withDensity L) :
    Measure.map (fun ω => H (X ω) (N ω)) (μ.restrict (X ⁻¹' {x})) =
      ρ.withDensity (fun y => μ (X ⁻¹' {x}) * L y) := by
  rw [map_observation_restrict_atom hX hN hi x hH, hNlaw, hDensity]
  exact (withDensity_smul _ hL).symm

theorem map_observation_restrict_atom_withDensity_ofReal [IsFiniteMeasure μ]
    [MeasurableSingletonClass α] {X : Ω → α} {N : Ω → β} {H : α → β → γ}
    {ν : Measure β} {ρ : Measure γ}
    (hX : Measurable X) (hN : Measurable N) (hi : IndepFun X N μ)
    (hNlaw : Measure.map N μ = ν) (x : α) (hH : Measurable (H x))
    {L : γ → ℝ} (hL : Measurable L)
    (hDensity : Measure.map (H x) ν = ρ.withDensity (fun y => ENNReal.ofReal (L y))) :
    Measure.map (fun ω => H (X ω) (N ω)) (μ.restrict (X ⁻¹' {x})) =
      ρ.withDensity (fun y => ENNReal.ofReal ((μ (X ⁻¹' {x})).toReal * L y)) := by
  rw [map_observation_restrict_atom_withDensity hX hN hi hNlaw x hH
    hL.ennreal_ofReal hDensity]
  congr 1
  funext y
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top μ _)]

end Problem336AdditiveD139.IndependentAtomLaw

end

end OAI
