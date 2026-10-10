import OAI.Probability.DilutedSpin.CountBridgeTools
import OAI.Probability.DilutedSpin.RootIntegralOrder

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma perturbedMean_averagedEnergyRoot
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample q) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    perturbedMean (N := N) μ ξ ν theta field Q m ψ r s =
      N*Real.log 2 + ∫ E,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ) E
        ∂compoundPoisson r (Measure.map (indexedPotential theta) (μ.prod (finiteUniform (Fin q → Fin N)))) := by
  let : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) theta) (μ.prod (finiteUniform (Fin q → Fin N)))) :=
    inferInstance
  rw [perturbedMean_energy_integral μ ξ ν r s theta field hθm hhm Q m hm ψ hC hD hθ hh hψ]
  congr 1
  exact integral_averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s _
    (compoundPoisson_integrable_id r _ (integrable_indexedPotential μ theta hθm hC hθ))
    (fun i : I×Fin N => Q i.1) m hm field hhm (locatedFactor ψ) hh
    (fun i _ a => hψ i.1 _ a)

/-- The actual new system differs from its reservoir-plus-cavity energy law
only by the double-new-coordinate rate. All physical field and mark averages
are retained, with their original counts and sites. -/
lemma perturbedMean_cavity_split
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (α s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (α*(N+1)) s -
      ((N+1:ℕ)*Real.log 2 + ∫ E,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) E
        ∂(compoundPoisson (reservoirRate α q N)
          (Measure.map (fun z : X × (Fin (q+1) → Fin N) =>
            indexedPotential theta (z.1,fun i => (z.2 i).succ))
            (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
        compoundPoisson (oneNewRate α q N)
          (Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
            indexedPotential theta (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
            (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N)))))))| ≤ C*cavityBadRate α q N := by
  rw [perturbedMean_averagedEnergyRoot μ ξ ν (α*(N+1)) s theta field hθm hhm Q m hm ψ hC hD hθ hh hψ,
    add_sub_add_left_eq_sub]
  exact cavity_split_lipschitz_bound μ α q N (indexedPotential theta)
    (measurable_indexedPotential theta hθm) hC
    (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by
      simpa only [Real.norm_eq_abs,indexedPotential] using hθ z.1 (fun i => σ (z.2 i))))
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s
      (fun i : I×Fin (N+1) => Q i.1) m hm field hhm (locatedFactor ψ) hh
      (fun i _ a => hψ i.1 _ a))

end DilutedSpinGlass.SizeCoupling

end

end OAI
