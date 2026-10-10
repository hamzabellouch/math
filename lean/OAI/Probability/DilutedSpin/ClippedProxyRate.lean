import OAI.Probability.DilutedSpin.ClippedCavityProxy
import OAI.Probability.DilutedSpin.PhysicalCavityPoisson
import OAI.Probability.DilutedSpin.PhysicalCavityRate

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {N L q : ℕ} [NeZero N]

lemma clippedSiteInsertion_rate_bound (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r t : ℝ≥0) :
    |clippedSiteInsertion M C H N L u r-clippedSiteInsertion M C H N L u t|≤
      C*|(r:ℝ)-t|+4*(scoreRate N:ℝ)/(N+1) := by
  have hθm σ : Measurable (fun z : InteractionSample (q+1) => (clipSample C z).1 σ) :=
    (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)
  have hθ z : ‖(clipSample (p := q+1) C z).1‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs] using clipSample_bound hC z σ)
  have hρ := reservoirEnergyLaw_integrable (N := N) M hC
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  have hFi := integrable_lipschitz_of_id (reservoirEnergyLaw M C N) hρ hF
  have hFb (E : (Fin N → Spin) → ℝ) : |reservoirEnergyRoot M H N L u E|≤‖E‖+(H*N+1*scoreRate N) := by
    simpa only [reservoirEnergyRoot,add_assoc] using averagedEnergyRoot_bound M.field.toMeasure
      ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
      (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (gridExponents_pos L)
      (clipReal H) (locatedFactor (spinFactor direction anchor u)) (fun y => clipReal_bound hH y)
      (fun i y a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a) E
  have hCi a := integrable_cavityPoissonValue M.disorder.toMeasure M.field.toMeasure
    (reservoirEnergyLaw M C N) hρ (clipSample C) (clipReal H) hθm (measurable_clipReal H)
    hC hH hθ (fun y => clipReal_bound hH y) hF.continuous hFb a
  have hh := averagedEnergyRoot_cavity_rate_bound M.disorder.toMeasure M.field.toMeasure (weights L)
    (reservoirEnergyLaw M C N) hρ r t (scoreRate N) (clipSample C) (clipReal H) hθm (measurable_clipReal H)
    (fun i : Spec L×ℕ => prior i.1) (gridExponents L) (gridExponents_pos L) (gridExponents_last L)
    (spinFactor direction anchor u) hH hC hθ (fun y => clipReal_bound hH y)
    (fun i σ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i σ a)
  unfold clippedSiteInsertion
  rw [insertionPoisson_site_energy M hC hH,insertionPoisson_site_energy M hC hH,
    integral_sub (hCi r) hFi,integral_sub (hCi t) hFi,sub_sub_sub_cancel_right]
  simpa only [mul_one,reservoirEnergyRoot] using hh

lemma clippedBondInsertion_rate_bound {p : ℕ} (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r t : ℝ≥0) :
    |clippedBondInsertion M C H N L u r-clippedBondInsertion M C H N L u t|≤C*|(r:ℝ)-t| := by
  let μ := Measure.map (indexedPotential (N := N) (clipSample (p := p) C))
    (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  have hb (z : InteractionSample p×(Fin p → Fin N)) : ‖indexedPotential (clipSample C) z‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs,indexedPotential,clipSample] using clipReal_bound hC (z.1.1 (fun i => σ (z.2 i))))
  have hi : Integrable id μ :=
    (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).mpr
      (Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hb))
  have hnorm : (∫ v,‖v‖ ∂μ)≤C := by
    rw [show (∫ v,‖v‖ ∂μ)=∫ z,‖indexedPotential (clipSample C) z‖
        ∂(M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))) from
      integral_map hm.aemeasurable continuous_norm.aestronglyMeasurable]
    exact (le_abs_self _).trans (abs_integral_le_bound (fun z => by simpa only [abs_of_nonneg (norm_nonneg _)] using hb z))
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  unfold clippedBondInsertion
  rw [insertionPoisson_bond_energy M hC hH,insertionPoisson_bond_energy M hC hH,
    ← integral_energyInsertionFunctional (reservoirEnergyLaw M C N) (compoundPoisson r μ) (compoundPoisson_integrable_id r μ hi) hF,
    ← integral_energyInsertionFunctional (reservoirEnergyLaw M C N) (compoundPoisson t μ) (compoundPoisson_integrable_id t μ hi) hF]
  exact (compoundPoisson_rate_bound r t μ hi (energyInsertionFunctional_lipschitz (reservoirEnergyLaw M C N) hF)).trans
    (by simpa only [NNReal.coe_one,one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_left hnorm (abs_nonneg ((r:ℝ)-t)))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
