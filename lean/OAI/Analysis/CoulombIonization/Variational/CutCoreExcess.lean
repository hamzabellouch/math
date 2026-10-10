import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpatialProductFactor
import OAI.Analysis.CoulombIonization.Variational.CorePriceExcess

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
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

def cutCoreExcess {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (Z lam : ℝ)
    (ψ : FormVector L) (b : Fin L → Fin 2) : ℝ :=
  cutCoreEnergy p hp Z ψ b+lam*cutCoreNumber b*formMass (orderedCutForm p hp ψ b)-
    priceEnergy (energy Z) lam*formMass (orderedCutForm p hp ψ b)

def cutExteriorPrice {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (Z lam : ℝ)
    (ψ : FormVector L) (b : Fin L → Fin 2) : ℝ :=
  formEnergy Z (orderedCutForm p hp ψ b)-cutCoreEnergy p hp Z ψ b+
    lam*cutOutNumber b*formMass (orderedCutForm p hp ψ b)

lemma cutCoreExcess_nonneg {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (b : Fin L → Fin 2) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) : 0 ≤ cutCoreExcess p hp Z lam ψ b := by
  have hh := cutCoreEnergy_priced p hp hψ b hZ hlam
  unfold cutCoreExcess
  rw [orderedCutForm_mass]
  linarith

theorem fresh_cut_field_envelope {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (b : Fin L → Fin 2) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) (t : Spins (cutOutNumber b)) :
    ∀ᵐ u, ∀ z ∈ closedBall y B,
      normalizedCoreField Z lam (coreSlice (orderedCutForm p hp ψ b) t u) z ≤
        coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ b) t u) := by
  apply ((orderedCutForm_core_antisymmetric p hp hψ b).ae_coreSlice
    (orderedCutForm_sobolev p hp hψ.sobolevVector b) t).mono
  intro u hu
  apply vacant_core_uniform_field_cap hu y hB hnuc _ hZ hlam
  intro x i hi
  exact (orderedCutForm_core_hole p hp ψ b (ball y (2*B)) hv hd (joinLists x u) i
    (by simpa only [joinLists_left] using hi)).coreSlice t

theorem fresh_cut_envelope_square {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (b : Fin L → Fin 2) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ t : Spins (cutOutNumber b), ∫ u,
      formMass (coreSlice (orderedCutForm p hp ψ b) t u)*
        (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ b) t u))^2) ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (orderedCutForm p hp ψ b)+
        cutCoreExcess p hp Z lam ψ b/B) :=
  integrated_core_envelope_square (orderedCutForm_core_antisymmetric p hp hψ b)
    (orderedCutForm_sobolev p hp hψ.sobolevVector b) hZ hlam hB

theorem fock_cut_envelope_square {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ b : Fin L → Fin 2, ∑ t : Spins (cutOutNumber b), ∫ u,
      formMass (coreSlice (orderedCutForm p hp ψ b) t u)*
        (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ b) t u))^2) ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass ψ+
        (∑ b : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ b)/B) := by
  have hh := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin L → Fin 2))) =>
    fresh_cut_envelope_square p hp hψ b hZ hlam hB)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_div,orderedCutForm_mass,
    spatial_cut_mass p hp hψ.sobolevVector] using hh

theorem fock_cut_excess_identity {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ b : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ b)+
      (∑ b : Fin L → Fin 2, cutExteriorPrice p hp Z lam ψ b) =
        corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p) := by
  rw [← Finset.sum_add_distrib]
  have hb (b : Fin L → Fin 2) :
      cutCoreExcess p hp Z lam ψ b+cutExteriorPrice p hp Z lam ψ b =
      formEnergy Z (orderedCutForm p hp ψ b)+
        (lam*L-priceEnergy (energy Z) lam)*formMass (orderedCutForm p hp ψ b) := by
    have hcard : (cutCoreNumber b : ℝ)+cutOutNumber b = L := by
      exact_mod_cast cutNumbers_sum b
    unfold cutCoreExcess cutExteriorPrice
    rw [← hcard]
    ring
  simp_rw [hb,orderedCutForm_energy,orderedCutForm_mass]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,spatial_cut_mass p hp hψ,
    spatial_cut_ims p hp hψ Z]
  unfold corePriceExcess weightedParticleCount
  ring

end CoulombAtom

end

end OAI
