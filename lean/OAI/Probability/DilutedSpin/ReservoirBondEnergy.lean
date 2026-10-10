import OAI.Probability.DilutedSpin.CavityInsertionFunctional
import OAI.Probability.DilutedSpin.CavityProxy
import OAI.Probability.DilutedSpin.ReservoirEnergyBounds

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L k : ℕ} [NeZero N]

lemma reservoirInsertionOn_site_energy (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (θ : Fin k → InteractionSample p) (h : ℝ) :
    reservoirInsertionOn M C H N L u (cavitySiteEnergy θ h)=
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect (fun j =>
        energyInsertionFunctional (reservoirEnergyLaw M C N) (reservoirEnergyRoot M H N L u)
          (fun σ => cavitySiteEnergy θ h (fun a => σ (j a.1 a.2)))) := by
  rw [reservoirInsertionOn_energy M C H hH]
  let e := Equiv.curry (Fin k) (Fin (p-1)) (Fin N)
  rw [FiniteLaw.uniform_expect,FiniteLaw.uniform_expect,Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma integral_reservoirInsertionOn_site (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (θ : Fin k → InteractionSample p) (hθ : ∀ a,‖(θ a).1‖≤C) :
    (∫ y,reservoirInsertionOn M C H N L u (cavitySiteEnergy θ (clipReal H y)) ∂M.field.toMeasure)=
      ∫ E,cavityArrayValue M.field.toMeasure id (clipReal H) (reservoirEnergyRoot M H N L u) E θ-
        reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N := by
  let F := reservoirEnergyRoot M H N L u
  let ρ := reservoirEnergyLaw M C N
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  simp_rw [reservoirInsertionOn_site_energy M C H hH]
  rw [FiniteLaw.integral_expect]
  · exact cavityArray_insertionFunctional ρ M.field.toMeasure id (clipReal H) (measurable_clipReal H)
      hF hH hC (fun y => clipReal_bound hH y) θ hθ
  · intro j
    apply Integrable.of_bound
      ((energyInsertionFunctional_lipschitz ρ hF).continuous.measurable.comp ?_).aestronglyMeasurable (H+C*k)
    · exact ae_of_all _ (fun y => by
        rw [Real.norm_eq_abs]
        apply (energyInsertionFunctional_bound ρ hF _).trans
        have hb := cavitySiteEnergy_norm_bound θ (clipReal H y) (fun a => j a.1 a.2) 0 hH hC hθ (clipReal_bound hH y)
        simpa only [Pi.zero_apply,zero_add,norm_zero] using hb)
    · apply Measurable.of_eval
      intro σ
      change Measurable (fun y => cavitySiteEnergy θ (clipReal H y) (fun a => σ (j a.1 a.2)))
      unfold cavitySiteEnergy
      apply Measurable.log
      apply Measurable.div_const
      apply Finset.measurable_sum
      intro ε _
      apply Measurable.exp
      exact ((measurable_clipReal H).mul_const _).add measurable_const

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L k : ℕ} [NeZero N]

lemma reservoirInsertionOn_bond_energy (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (θ : Fin k → InteractionSample p) :
    reservoirInsertionOn M C H N L u (cavityBondEnergy θ)=
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect (fun j =>
        energyInsertionFunctional (reservoirEnergyLaw M C N) (reservoirEnergyRoot M H N L u)
          (∑ i,indexedPotential id (θ i,j i))) := by
  rw [reservoirInsertionOn_energy M C H hH]
  let e := Equiv.curry (Fin k) (Fin p) (Fin N)
  rw [FiniteLaw.uniform_expect,FiniteLaw.uniform_expect,Fintype.card_congr e]
  congr 1
  apply Fintype.sum_equiv e
  intro j
  have he : (fun σ => cavityBondEnergy θ (fun a => σ (j a)))=
      (∑ i,indexedPotential id (θ i,e j i)) := by
    ext σ
    simp [cavityBondEnergy,indexedPotential,e]
  unfold energyInsertionFunctional
  rw [he]

lemma insertionPoisson_bond_energy (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) :
    insertionPoisson M C H N L u
      (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
      (fun _ θ => cavityBondEnergy (fun j => clipSample C (θ j))) r=
      ∫ E,∫ v,reservoirEnergyRoot M H N L u (E+v)-reservoirEnergyRoot M H N L u E
        ∂compoundPoisson r (Measure.map (indexedPotential (N := N) (clipSample C))
          (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))))
        ∂reservoirEnergyLaw M C N := by
  let μ := Measure.map (indexedPotential (N := N) (clipSample C))
    (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  have hμ : Integrable id μ := integrable_indexedPotential M.disorder.toMeasure (clipSample C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)) hC
    (fun z σ => clipReal_bound hC _)
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  rw [← integral_energyInsertionFunctional (reservoirEnergyLaw M C N)
    (compoundPoisson r μ) (compoundPoisson_integrable_id r μ hμ) hF]
  rw [integral_compound_finite_sample M.disorder.toMeasure (indexedPotential (N := N) (clipSample C)) hm
    (C := C) (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by
      simpa only [Real.norm_eq_abs,indexedPotential,clipSample] using clipReal_bound hC (z.1.1 (fun i => σ (z.2 i))))) r
    (energyInsertionFunctional_lipschitz (reservoirEnergyLaw M C N) hF)]
  unfold insertionPoisson
  apply integral_congr_ae
  filter_upwards [] with k
  apply integral_congr_ae
  filter_upwards [] with θ
  exact reservoirInsertionOn_bond_energy M C H hH u (fun j => clipSample C (θ j))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
