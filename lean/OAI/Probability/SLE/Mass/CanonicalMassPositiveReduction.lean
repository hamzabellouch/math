import OAI.Probability.SLE.Mass.PositiveMassGerm
import OAI.Probability.SLE.Mass.CanonicalMassNontrivial

namespace OAI

/-! The remaining scaling link in positive canonical mass: equal
nonzero-mass probabilities at positive times suffice, with the Green
mean and the Brownian germ argument already proved. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem positive_all_times_of_scaling
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hscale : ∀ s t : ℝ≥0, 0<s → 0<t →
      P {ω | C.process s ω≠0}=P {ω | C.process t ω≠0}) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0<t → C.process t ω≠0 := by
  obtain ⟨n,hn⟩ := C.exists_nonzero_finite_time
  have hN : 0<P {ω | C.process (n+1) ω≠0} := by
    apply hn.trans_le
    apply measure_mono_ae
    filter_upwards [C.paths] with ω hω
    intro hp
    have hle := hω.monotone (show (n:ℝ≥0)≤n+1 from le_add_of_nonneg_right zero_le)
    intro hz
    apply hp
    rw [hz] at hle
    exact le_antisymm hle bot_le
  let ε : ℕ → ℝ≥0 := fun j => 1/((j:ℝ≥0)+1)
  have hεp (j : ℕ) : 0<ε j := by dsimp [ε]; positivity
  have hεa : Antitone ε := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hZa : Adapted (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable))
      (fun t ω => C.process t ω univ) := by
    intro t
    exact (Measure.measurable_coe MeasurableSet.univ).comp (C.progressive.adapted t)
  have hZm : ∀ᵐ ω ∂P, Monotone (fun t => C.process t ω univ) :=
    C.paths.mono (fun _ h => fun _ _ hst => h.monotone hst univ)
  have hp := positive_mass_all_times_of_uniform_probability hB
    (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0
    (fun t ω => C.process t ω univ) hZa hZm ε hεa hε
    (P {ω | C.process (n+1) ω≠0}) hN (fun j => by
      simp only [Measure.measure_univ_pos]
      exact le_of_eq (hscale (n+1) (ε j) (by positivity) (hεp j)))
  filter_upwards [hp] with ω hω
  intro t ht
  exact Measure.measure_univ_pos.mp (hω t ht)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
