import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.IntegratedStability
import OAI.Analysis.CoulombIonization.Fermionic.MultiplierError
import OAI.Analysis.CoulombIonization.Variational.SpinJoinEquiv

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

theorem quantum_sector_near_minimizer (Z : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖ ^ 2 = 1 ∧
      formEnergy Z (graphFormVector F) < energy Z N + ε := by
  have hex : ∃ ψ : FormVector N, FormAdmissible ψ ∧
      formEnergy Z ψ < energy Z N + ε := by
    by_cases hN : N = 0
    · subst N
      obtain ⟨ψ, hψ⟩ := formDomain_nonempty 0
      refine ⟨ψ, hψ, ?_⟩
      simpa only [formEnergy, Fin.sum_univ_zero, Finset.sum_const_zero,
        mul_zero, sub_zero, add_zero, energy, ↓reduceIte, zero_add] using hε
    · have hh : sInf {e | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} <
          energy Z N + ε := by
        simpa only [energy, ite_eq_right hN] using (lt_add_of_pos_right (energy Z N) hε)
      obtain ⟨e, ⟨ψ, hψ, he⟩, he'⟩ := exists_lt_of_csInf_lt (formValues_nonempty Z N) hh
      exact ⟨ψ, hψ, he ▸ he'⟩
  obtain ⟨ψ, hψ, he⟩ := hex
  refine ⟨admissibleGraph ψ hψ, admissibleGraph_norm ψ hψ, ?_⟩
  have heq := formEnergy_congr_ae Z (graphFormVector (admissibleGraph ψ hψ)) ψ
    (graphFormVector_admissibleGraph_value ψ hψ)
    (graphFormVector_admissibleGraph_gradient ψ hψ)
  exact heq ▸ he

lemma quantum_price_le_sector {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) (N : ℕ) :
    priceEnergy (energy Z) lam ≤ energy Z N + lam * N := by
  obtain ⟨n, hn⟩ := quantum_exists_priceMinimizes hZ hlam
  rw [priceEnergy_eq_of_minimizes hn]
  exact hn N

theorem quantum_priced_near_minimizer {Z lam ε : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ F : fermionGraph n, ‖fermionGraphValue n F‖ ^ 2 = 1 ∧
      formEnergy Z (graphFormVector F) + lam * n < priceEnergy (energy Z) lam + ε := by
  obtain ⟨n, hn⟩ := quantum_exists_priceMinimizes hZ hlam
  obtain ⟨F, hF, he⟩ := quantum_sector_near_minimizer Z n hε
  refine ⟨n, F, hF, ?_⟩
  rw [priceEnergy_eq_of_minimizes hn]
  linarith

theorem SobolevFermion.priced_lower_bound {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam * formMass ψ ≤
      formEnergy Z ψ + lam * N * formMass ψ := by
  have hp := mul_le_mul_of_nonneg_right (quantum_price_le_sector hZ hlam N)
    (formMass_nonneg ψ)
  have he := hψ.energy_mul_mass_le hZ
  nlinarith

theorem conditional_core_priced_energy {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (t : Spins M) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    ∀ᵐ y, priceEnergy (energy Z) lam * formMass (coreSlice ψ t y) ≤
      formEnergy Z (coreSlice ψ t y) + lam * N * formMass (coreSlice ψ t y) :=
  (hψ.ae_coreSlice t).mono fun _ hy => hy.priced_lower_bound hZ hlam

theorem integrated_core_priced_energy {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam * formMass ψ ≤
      (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y)) + lam * N * formMass ψ := by
  have hp := mul_le_mul_of_nonneg_right (quantum_price_le_sector hZ hlam N)
    (formMass_nonneg ψ)
  have he := integrated_core_energy hψ hZ
  nlinarith

theorem quantum_priced_partition_excess {Z lam ε : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N : ℕ} (F : fermionGraph N) (hF : ‖fermionGraphValue N F‖ ^ 2 = 1)
    (he : formEnergy Z (graphFormVector F) + lam * N ≤ priceEnergy (energy Z) lam + ε)
    (p q : FermionMultiplier N) (hpq : ∀ x, p.value x ^ 2 + q.value x ^ 2 = 1) :
    formEnergy Z (graphFormVector (p.apply F)) +
      (lam * N - priceEnergy (energy Z) lam) * ‖fermionGraphValue N (p.apply F)‖ ^ 2 ≤
        ε + multiplierError p F + multiplierError q F := by
  have hb : priceEnergy (energy Z) lam - lam * N ≤ energy Z N := by
    linarith [quantum_price_le_sector hZ hlam N]
  have hi := quantum_partition_excess hZ hb p q hpq F
  rw [hF, mul_one] at hi
  nlinarith

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
