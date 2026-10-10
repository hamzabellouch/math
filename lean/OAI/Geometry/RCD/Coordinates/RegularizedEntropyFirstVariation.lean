import OAI.Geometry.RCD.Coordinates.RegularizedEntropySecant
import OAI.Geometry.RCD.Heat.EntropyPowerFirstVariation

namespace OAI

/-! # Finite-dimensional first variation for the actual regularized log direction -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem regularized_entropy_power_first_variation (μ : Measure X) [SigmaFinite μ]
    (ν₀ : Measure X) [IsProbabilityMeasure ν₀]
    (r : Lp ℝ 2 μ) {h : X → ℝ}
    (hr : (r : X → ℝ) =ᵐ[μ] fun x => h x^2)
    (hrn : (fun x => h x^2) =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B)
    (het : ∀ t : Time, Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
      Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ)
    {N : ℝ} (hN : 0 < N) {V : ℝ → ℝ} {D d : ℝ}
    (hV0 : V 0=Real.exp (-boltzmannEntropy μ ν₀/N))
    (hV : HasDerivAt V D 0)
    (hp : ∀ t : Time, V t ≤ Real.exp (-boltzmannEntropy μ (π.map (fun γ => γ t))/N))
    (hd : Tendsto (regularizedPlanLogSecant π h) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    d ≤ -N*(D/(V 0)) := by
  let E : ℝ → ℝ := fun t => boltzmannEntropy μ (π.map (fun γ => geodesicExtension γ t))
  have hE (t : Time) : E t=boltzmannEntropy μ (π.map (fun γ => γ t)) := by
    simp only [E,geodesicExtension_eq]
  have hEzero : E 0=boltzmannEntropy μ ν₀ := by
    simpa [hmap0] using hE (0:Time)
  have hVpos : 0 < V 0 := by rw [hV0]; exact Real.exp_pos _
  have hE0 : E 0 = -N*Real.log (V 0) := by
    rw [hV0,Real.log_exp,hEzero]
    field_simp
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  apply entropy_power_first_variation (M := (μ B).toReal) hN hVpos hV hE0 _ _ hd
  · filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    rw [hE (⟨t,ht0.le,ht1.le⟩:Time)]
    exact hp ⟨t,ht0.le,ht1.le⟩
  · filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    have hh := regularized_log_secant_le_entropy μ ν₀ r hr hrn he0 π hmap0 hC hcomp
      hB hs ⟨t,ht0.le,ht1.le⟩ ht0 (het _)
    rw [hEzero,hE (⟨t,ht0.le,ht1.le⟩:Time)]
    exact hh

end RegularPointCoordinates

end

end OAI
