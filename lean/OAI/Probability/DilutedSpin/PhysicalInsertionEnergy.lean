import OAI.Probability.DilutedSpin.CountBridgeTools
import OAI.Probability.DilutedSpin.FullRootIncrement

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower ConcreteReservoir
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I] in
lemma rootInsertion_energyRoot
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) (z : FullRootState Y X I N) (i : Fin a → Site N) :
    rootInsertion (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
      (fun h k x y => energy V field h k x (terminalState L y)) factor
      (fun y s => readSpin (terminalState L y) s) a F (z,i) =
    energyRoot Q m field factor z.1 z.2.2
      ((∑ j,V (rootArray z.2.1.1 z.2.1.2 j))+(fun σ => F (fun j => readSpin σ (i j))))-
      energyRoot Q m field factor z.1 z.2.2 (∑ j,V (rootArray z.2.1.1 z.2.1.2 j)) := by
  rw [rootInsertion_eq_difference]
  unfold energyRoot
  apply congrArg₂ (fun x y : ℝ => x-y)
  · congr 1
    funext y
    simp only [energy,Pi.add_apply,Finset.sum_apply]
    ring
  · simp only [energy,Finset.sum_apply]

lemma fullRoot_sameInsertion_energy
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (hV : Measurable V)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    (∫ z : FullRootState Y X I N,
      sameInsertionAverage (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
        (fun h k x y => energy V field h k x (terminalState L y)) factor
        (fun y i => readSpin (terminalState L y) i) a F z
      ∂fullRootLaw (fun _ => ξ) μ ν r s) =
    (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
      ∫ E,averagedEnergyRoot ξ ν s Q m field factor (E+(fun σ => F (fun j => readSpin σ (i j))))-
        averagedEnergyRoot ξ ν s Q m field factor E
        ∂compoundPoisson r (Measure.map V μ)) := by
  unfold sameInsertionAverage
  rw [FiniteLaw.integral_expect_bounded (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)) (fullRootLaw (fun _ => ξ) μ ν r s) (B := ‖F‖)]
  · apply FiniteLaw.expect_congr
    intro i
    simp only [rootInsertion_energyRoot]
    exact fullRoot_energy_increment ξ μ ν r s V hV Q m hm field hfield factor hh hf _
  · intro i
    exact (measurable_rootInsertion _ Q m _ factor _
      (fun k _ => measurable_energy V field (fun σ => (measurable_pi_apply σ).comp hV) hfield k _) a F).comp
        (measurable_id.prodMk measurable_const)
  · intro z i
    exact backwardLog_bound (L+1) _ m hm (fun _ => norm_le_pi_norm F _)

end DilutedSpinGlass.PhysicalRoot

end

end OAI
