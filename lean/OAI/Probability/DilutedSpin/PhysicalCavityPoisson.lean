import OAI.Probability.DilutedSpin.FullRootIncrement
import OAI.Probability.DilutedSpin.PhysicalCavitySplit

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PhysicalRoot
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma averagedEnergyRoot_newSpin_poisson
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    |(∫ v,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
        (fun σ => E (fun i => σ i.succ)+v σ)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))))-
      (∫ k,∫ z : Fin k → X,cavityArrayValue ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) E z
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)|≤2*D*s/(N+1) := by
  apply cavity_poisson_bridge μ ξ theta field hθm hhm hH hC hθ hh
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin N))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous
    (fun v => by
      simpa only [add_assoc] using averagedEnergyRoot_bound ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m hm field (locatedFactor ψ) hh (fun i y a => hf i.1 _ a) v)
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)) E r
  intro k z j
  exact averagedEnergyRoot_newSpin ξ ν s Q m hm hend ψ field hhm E
    (fun a => theta (z a)) (fun a => j a.1 a.2) hH hh hf

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p : ℕ} [NeZero N]

lemma integrable_cavityPoissonValue
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    (θ : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (θ x).1 σ)) (hhm : Measurable field)
    {C H B : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ x,‖(θ x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (hFb : ∀ E,|F E|≤‖E‖+B)
    (r : ℝ≥0) : Integrable (cavityPoissonValue μ ξ θ field F r) ρ := by
  have hb E : |cavityPoissonValue μ ξ θ field F r E|≤‖E‖+(H+C*r+B) := by
    simpa only [add_assoc] using cavityPoissonValue_bound μ ξ θ field hH hC hθ hh hFb r E
  exact (hρ.norm.add (integrable_const (H+C*r+B))).mono'
    (measurable_cavityPoissonValue μ ξ θ field hθm hhm hF r).aestronglyMeasurable
    (ae_of_all _ (fun E => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using hb E))

end DilutedSpinGlass

end

end OAI
