import OAI.Probability.DilutedSpin.CavityGapFubini
import OAI.Probability.DilutedSpin.ReservoirBondEnergy

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma insertionPoisson_site_energy (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) :
    insertionPoisson M C H N L u
      (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
      (fun _ z => cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2)) r=
      ∫ E,cavityPoissonValue M.disorder.toMeasure M.field.toMeasure (clipSample C) (clipReal H)
        (reservoirEnergyRoot M H N L u) r E-reservoirEnergyRoot M H N L u E
        ∂reservoirEnergyLaw M C N := by
  have hclip (z : InteractionSample p) : ‖(clipSample C z).1‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs,clipSample] using clipReal_bound hC (z.1 σ))
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  have ha (k : ℕ) :
      (∫ z : (Fin k → InteractionSample p)×ℝ,
        reservoirInsertionOn M C H N L u (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))
        ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)=
      ∫ θ : Fin k → InteractionSample p,∫ E,
        cavityArrayValue M.field.toMeasure (clipSample C) (clipReal H) (reservoirEnergyRoot M H N L u) E θ-
          reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
    have hm : Measurable (fun z : (Fin k → InteractionSample p)×ℝ =>
        reservoirInsertionOn M C H N L u (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))) := by
      simp_rw [reservoirInsertionOn_site_energy M C H hH]
      apply FiniteLaw.measurable_expect
      intro j
      apply (energyInsertionFunctional_lipschitz (reservoirEnergyLaw M C N) hF).continuous.measurable.comp
      convert measurable_cavityArrayEnergy (N := N) (p := p) (k := k) (clipSample C) (clipReal H)
          (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
          (measurable_clipReal H) (0 : (Fin N → Spin) → ℝ) j using 1
      ext z σ
      simp [cavityArrayEnergy]
    have hb (z : (Fin k → InteractionSample p)×ℝ) : |reservoirInsertionOn M C H N L u
        (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))|≤H+C*k := by
      apply reservoirInsertionOn_bound
      intro σ
      apply (cavitySiteEnergy_bound _ _ σ).trans
      have hs : (∑ j : Fin k,‖(clipSample C (z.1 j)).1‖)≤C*k := by
        simpa [mul_comm] using Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin k))) => hclip (z.1 j))
      exact add_le_add (clipReal_bound hH _) hs
    rw [integral_prod _ (Integrable.of_bound hm.aestronglyMeasurable (H+C*k)
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb z)))]
    apply integral_congr_ae
    filter_upwards [] with θ
    exact integral_reservoirInsertionOn_site M hC hH u (fun j => clipSample C (θ j)) (fun _ => hclip _)
  unfold insertionPoisson
  simp_rw [ha]
  exact cavityPoisson_gap_fubini M.disorder.toMeasure M.field.toMeasure (reservoirEnergyLaw M C N)
    (clipSample C) (clipReal H)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
    (measurable_clipReal H) hF hH hC hclip (fun y => clipReal_bound hH y) r

end DilutedSpinGlass.UniversalDictionary

end

end OAI
