import OAI.Probability.DilutedSpin.CavitySiteMean
import OAI.Probability.DilutedSpin.ReservoirInsertionEnergy

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

noncomputable def variableSiteInsertion (M : Model p) (C H : ℝ)
    (u : Spec L×ℕ → ℝ) (b : ℕ) (F : (Fin b → Spin) → ℝ) (d : ℕ) [NeZero d] : ℝ :=
  let rd := fun (σ : Fin N → Spin) (i : Fin d) => if h : i.val<N then σ ⟨i.val,h⟩ else false
  let ψ := fun (i : (Spec L×ℕ)×Fin d) (y : FinitePath (Fin N → Spin) (L+1))
    (a : FinitePath (Alphabet i.1.1) (L+1)) => spinFactor direction anchor u i.1 (rd (terminalState L y) i.2) a
  (FiniteLaw.uniform : FiniteLaw (Fin b → Fin d)).expect (fun i =>
    ∫ E,averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin d))) (scoreRate N)
        (fun i : (Spec L×ℕ)×Fin d => prior i.1.1) (gridExponents L) (clipReal H) ψ
        (E+(fun σ => F (fun j => rd σ (i j))))-
      averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin d))) (scoreRate N)
        (fun i : (Spec L×ℕ)×Fin d => prior i.1.1) (gridExponents L) (clipReal H) ψ E
      ∂compoundPoisson (reservoirRate M.alpha (p-1) N)
        (Measure.map (fun z : InteractionSample p × (Fin p → Fin d) =>
          fun σ => clipReal C (z.1.1 (fun j => rd σ (z.2 j))))
          (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin d)))))

lemma reservoirInsertion_energy_positive (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (b : ℕ) (F : (Fin b → Spin) → ℝ) :
    reservoirInsertion M C H N L u b F=
      (FiniteLaw.uniform : FiniteLaw (Fin b → Fin N)).expect (fun i =>
        ∫ E,averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
            (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (clipReal H)
            (locatedFactor (spinFactor direction anchor u))
            (E+(fun σ => F (fun j => σ (i j))))-
          averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
            (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (clipReal H)
            (locatedFactor (spinFactor direction anchor u)) E
          ∂compoundPoisson (reservoirRate M.alpha (p-1) N)
            (Measure.map (fun z : InteractionSample p × (Fin p → Fin N) =>
              fun σ => clipReal C (z.1.1 (fun j => σ (z.2 j))))
              (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))))) := by
  have he := reservoirInsertion_energy M C H hH N L u (D := 1)
    (fun i y a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a) b F
  rw [he]
  change variableSiteInsertion (N := N) M C H u b F (max N 1)=_
  have hmax : max N 1=N := max_eq_left (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  simp only [hmax]
  unfold variableSiteInsertion
  simp only [Fin.is_lt,↓reduceDIte,Fin.eta]
  rfl

end DilutedSpinGlass.UniversalDictionary

end

end OAI
