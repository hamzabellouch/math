import Mathlib
import OAI.Analysis.CoulombIonization.Variational.Spatial

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
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma SobolevVector.coreSlice_mass_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) :
    Integrable (fun y => formMass (coreSlice ψ t y)) := by
  apply integrable_finsetSum
  intro s _
  simpa only [coreSlice] using
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).integral_prod_right

lemma SobolevVector.integral_coreSlice_mass {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y, formMass (coreSlice ψ t y)) = formMass ψ := by
  simp only [formMass, coreSlice]
  have h (s : Spins N) (t : Spins M) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖ ^ 2) :=
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).integral_prod_right
  simp_rw [integral_finsetSum _ (fun s _ => h s _)]
  simp_rw [integral_join (hψ.1 _).norm.integrable_sq]
  exact sum_spin_join (fun u => ∫ z, ‖ψ.value u z‖ ^ 2)

lemma SobolevVector.coreSlice_energy_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z : ℝ) (t : Spins M) :
    Integrable (fun y => formEnergy Z (coreSlice ψ t y)) := by
  have hk (s : Spins N) (i : Fin N) (a : Fin 3) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).gradient s i a x‖ ^ 2) := by
    exact (integrable_join (N := N) (M := M)
      (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).norm.integrable_sq).integral_prod_right
  have hn (s : Spins N) (i : Fin N) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖ ^ 2 / ‖x i‖) := by
    have hh := (integrable_join (N := N) (M := M)
      (CoulombAtom.nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  have hp (s : Spins N) (i j : Fin N) (hij : i < j) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖ ^ 2 / ‖x i-x j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun he => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective he))
    have hh := (integrable_join (N := N) (M := M)
      (CoulombAtom.pair_integrable (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) hne
        (hψ.1 (joinLists s t)) (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  unfold formEnergy
  apply Integrable.add
  · apply Integrable.sub
    · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun a _ => hk s i a)))).const_mul _
    · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
        hn s i))).const_mul _
  · apply integrable_finsetSum; intro s _
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp s i j hij
    · exact integrable_zero _ _ _

theorem CoreAntisymmetric.integrated_priced {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam * formMass ψ ≤
      (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y)) + lam * N * formMass ψ := by
  rw [← hψ.integral_coreSlice_mass, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hψ.coreSlice_energy_integrable Z t)
      ((hψ.coreSlice_mass_integrable t).const_mul _)]
  exact integral_mono_ae ((hψ.coreSlice_mass_integrable t).const_mul _)
    ((hψ.coreSlice_energy_integrable Z t).add
      ((hψ.coreSlice_mass_integrable t).const_mul _))
    ((ha.ae_coreSlice hψ t).mono fun _ h => h.priced_lower_bound hZ hlam)

theorem spatial_core_energy_priced {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    let q := multiplyForm (spatialProduct p hp (coreCutLabels N M)) ψ
    priceEnergy (energy Z) lam * formMass q ≤
      (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice q t y)) + lam * N * formMass q := by
  apply CoreAntisymmetric.integrated_priced _ (hψ.sobolevVector.multiply _) hZ hlam
  apply hψ.coreAntisymmetric.multiply
  intro π x
  exact spatialProduct_invariant p _ (corePerm M π) (coreCutLabels_invariant π) x

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
