import OAI.Probability.DilutedSpin.ReservoirSiteTransport

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

noncomputable def reservoirEnergyRoot (M : Model p) (H : ℝ) (N L : ℕ) [NeZero N]
    (u : Spec L×ℕ → ℝ) : ((Fin N → Spin) → ℝ) → ℝ :=
  averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
    (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (clipReal H)
    (locatedFactor (spinFactor direction anchor u))

noncomputable def reservoirEnergyLaw (M : Model p) (C : ℝ) (N : ℕ) [NeZero N] :
    Measure ((Fin N → Spin) → ℝ) :=
  compoundPoisson (reservoirRate M.alpha (p-1) N)
    (Measure.map (fun z : InteractionSample p × (Fin p → Fin N) =>
      fun σ => clipReal C (z.1.1 (fun j => σ (z.2 j))))
      (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))))

lemma reservoirInsertionOn_energy {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ) :
    reservoirInsertionOn M C H N L u F=
      (FiniteLaw.uniform : FiniteLaw (ι → Fin N)).expect (fun i =>
        ∫ E,reservoirEnergyRoot M H N L u (E+(fun σ => F (fun j => σ (i j))))-
          reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N) := by
  unfold reservoirInsertionOn
  rw [reservoirInsertion_energy_positive M C H hH]
  let e : (Fin (Fintype.card ι) → Fin N) ≃ (ι → Fin N) :=
    Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl (Fin N))
  rw [FiniteLaw.uniform_expect,FiniteLaw.uniform_expect,Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
