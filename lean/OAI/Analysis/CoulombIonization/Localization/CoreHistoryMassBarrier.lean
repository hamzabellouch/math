import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CoreHistoryFermionBarrier
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryAverageBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

lemma sum_nextCoreObservation_mass {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) :
    (∑ c : Fin N → Fin 2, formMass (nextCoreObservation p hp ψ c)) = formMass ψ := by
  simp_rw [coreLawAverage_next_mass hψ p hp]
  rw [Finset.sum_comm]
  rw [←hψ.integral_coreSlice_mass]
  apply Finset.sum_congr rfl
  intro t _
  rw [←integral_finsetSum _ (fun c _ => nextCoreObservation_mass_statistic_integrable hψ p hp c t)]
  apply integral_congr_ae
  filter_upwards [hψ.ae_coreSlice t] with v hv
  simp only [orderedCutForm_mass,spatial_cut_mass p hp hv]

lemma sum_nextCoreObservation_excess {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (Z lam : ℝ) :
    (∑ c : Fin N → Fin 2,
      coreLawAverage (nextCoreObservation p hp ψ c) (corePriceExcess Z lam)) =
      ∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2, cutCoreExcess p hp Z lam (coreSlice ψ t v) c := by
  simp_rw [coreLawAverage_next_excess hψ p hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact (integral_finsetSum _ (fun c _ =>
    nextCoreObservation_excess_statistic_integrable hψ p hp c t Z lam)).symm

structure CoreObservationGraph where
  coreSize : ℕ
  outSize : ℕ
  vector : FormVector (coreSize+outSize)
  sobolev : SobolevVector vector
  antisymmetric : CoreAntisymmetric vector

namespace CoreObservationGraph

def initial {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) : CoreObservationGraph where
  coreSize := N
  outSize := 0
  vector := ψ
  sobolev := hψ.sobolevVector
  antisymmetric := hψ.coreAntisymmetric

def observe (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin G.coreSize → Fin 2) : CoreObservationGraph where
  coreSize := cutCoreNumber c
  outSize := cutOutNumber c+G.outSize
  vector := nextCoreObservation p hp G.vector c
  sobolev := nextCoreObservation_sobolev G.sobolev p hp c
  antisymmetric := nextCoreObservation_antisymmetric G.antisymmetric p hp c

def mass (G : CoreObservationGraph) : ℝ := formMass G.vector

def coreAverage (G : CoreObservationGraph) (F : ∀ N, FormVector N → ℝ) : ℝ :=
  coreLawAverage G.vector (F G.coreSize)

lemma observe_mass (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) :
    (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).mass) = G.mass :=
  sum_nextCoreObservation_mass G.sobolev p hp

lemma mass_nonneg (G : CoreObservationGraph) : 0 ≤ G.mass := formMass_nonneg _

lemma observe_total_size (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin G.coreSize → Fin 2) :
    (G.observe p hp c).coreSize+(G.observe p hp c).outSize = G.coreSize+G.outSize := by
  change cutCoreNumber c+(cutOutNumber c+G.outSize) = _
  rw [←Nat.add_assoc,cutNumbers_sum]

end CoreObservationGraph
end CoulombAtom

end

end OAI
