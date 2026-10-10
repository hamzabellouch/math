import OAI.Probability.DilutedSpin.InsertionPoint
import OAI.Probability.DilutedSpin.PhysicalCountLaw

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ} [NeZero N]

/-- The literal perturbed physical mean as a compound Poisson energy integral.
Counts, index repetitions, fields, and the full marked reservoir are retained. -/
lemma perturbedMean_energy_integral
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    perturbedMean (N := N) μ ξ ν theta field Q m ψ r s =
      N*Real.log 2 + ∫ h,∫ a,∫ E,energyRoot (fun i : I×Fin N => Q i.1) m field
        (locatedFactor ψ) h a E
        ∂compoundPoisson r (Measure.map (indexedPotential theta) (μ.prod (finiteUniform (Fin p → Fin N))))
        ∂compoundRootLaw (ν.prod (finiteUniform (Fin N))) s ∂rootLaw N (fun _ => ξ) := by
  unfold perturbedMean
  congr 1
  rw [← fullRoot_countedMean μ ξ ν r s theta field hθm hhm Q m hm ψ hC hD hθ hh hψ]
  exact fullRoot_energy_integral ξ (μ.prod (finiteUniform (Fin p → Fin N)))
    (ν.prod (finiteUniform (Fin N))) r s (indexedPotential theta) field
    (measurable_indexedPotential theta hθm) hhm (fun i : I×Fin N => Q i.1) m hm
    (locatedFactor ψ) hC hD (fun z σ => hθ z.1 _) hh (fun i y a => hψ i.1 _ a)

lemma integrable_indexedPotential
    (μ : Measure X) [IsProbabilityMeasure μ] (theta : X → InteractionSample p)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ))
    {C : ℝ} (hC : 0≤C) (hθ : ∀ x σ,|(theta x).1 σ|≤C) :
    Integrable id (Measure.map (indexedPotential (N := N) theta) (μ.prod (finiteUniform (Fin p → Fin N)))) := by
  apply (integrable_map_measure measurable_id.aestronglyMeasurable (measurable_indexedPotential theta hθm).aemeasurable).mpr
  apply (integrable_const C).mono' (measurable_indexedPotential theta hθm).aestronglyMeasurable
  exact ae_of_all _ (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs, indexedPotential, id_eq] using hθ z.1 (fun l => σ (z.2 l))))

lemma indexedPotential_norm_integral_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (theta : X → InteractionSample p)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ))
    {C : ℝ} (hC : 0≤C) (hθ : ∀ x σ,|(theta x).1 σ|≤C) :
    (∫ E : (Fin N → Spin) → ℝ,‖E‖ ∂Measure.map (indexedPotential theta) (μ.prod (finiteUniform (Fin p → Fin N))))≤C := by
  rw [integral_map (measurable_indexedPotential theta hθm).aemeasurable (by fun_prop)]
  apply (integral_mono (integrable_indexedPotential μ theta hθm hC hθ |>.norm |>.comp_measurable
    (measurable_indexedPotential theta hθm)) (integrable_const C) ?_).trans_eq (by simp)
  intro z
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs, indexedPotential, id_eq] using hθ z.1 (fun l => σ (z.2 l)))

end DilutedSpinGlass.SizeCoupling

end

end OAI
