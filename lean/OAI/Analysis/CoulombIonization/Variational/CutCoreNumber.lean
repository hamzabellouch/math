import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpatialErrorWeight
import OAI.Analysis.CoulombIonization.FormDomain.CoreSliceMassIntegrable
import OAI.Analysis.CoulombIonization.Variational.SumPairsHalf

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
namespace CoulombAtom

abbrev cutCoreNumber {L : ℕ} (b : Fin L → Fin 2) : ℕ := Fintype.card {i // b i = 0}
abbrev cutOutNumber {L : ℕ} (b : Fin L → Fin 2) : ℕ := Fintype.card {i // b i ≠ 0}

def cutOrder {L : ℕ} (b : Fin L → Fin 2) :
    Fin (cutCoreNumber b + cutOutNumber b) ≃ Fin L :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr
    (Fintype.equivFin {i // b i = 0}).symm (Fintype.equivFin {i // b i ≠ 0}).symm).trans
      (Equiv.sumCompl (fun i => b i = 0)))

lemma cutNumbers_sum {L : ℕ} (b : Fin L → Fin 2) : cutCoreNumber b + cutOutNumber b = L := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (cutOrder b)

lemma cutOrder_labels {L : ℕ} (b : Fin L → Fin 2) :
    b ∘ cutOrder b = coreCutLabels (cutCoreNumber b) (cutOutNumber b) := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · change b (cutOrder b (finSumFinEquiv (Sum.inl j))) = _
    simp only [cutOrder, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl, coreCutLabels, joinLists_left]
    exact ((Fintype.equivFin {i // b i = 0}).symm j).property
  · change b (cutOrder b (finSumFinEquiv (Sum.inr j))) = _
    simp only [cutOrder, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr, coreCutLabels, joinLists_right]
    have hh := ((Fintype.equivFin {i // b i ≠ 0}).symm j).property
    omega

lemma spatialProductValue_reindex {M N : ℕ} (e : Fin M ≃ Fin N)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (b : Fin N → Fin 2) (x : Configuration M) :
    spatialProductValue p b (x ∘ e.symm) = spatialProductValue p (b ∘ e) x := by
  unfold spatialProductValue
  rw [← Equiv.prod_comp e (fun i => (p (b i)).value ((x ∘ e.symm) i))]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

def orderedCutForm {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) :
    FormVector (cutCoreNumber b + cutOutNumber b) :=
  reindexForm (cutOrder b) (multiplyForm (spatialProduct (N := L) p hp b) ψ)

lemma orderedCutForm_value {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) (s) (x) :
    (orderedCutForm p hp ψ b).value s x =
      (multiplyForm (spatialProduct p hp (coreCutLabels (cutCoreNumber b) (cutOutNumber b)))
        (reindexForm (cutOrder b) ψ)).value s x := by
  change (spatialProductValue p b (x ∘ (cutOrder b).symm) : ℂ) * _ = _
  rw [spatialProductValue_reindex, cutOrder_labels]
  rfl

lemma orderedCutForm_sobolev {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevVector ψ) (b : Fin L → Fin 2) :
    SobolevVector (orderedCutForm p hp ψ b) :=
  (hψ.multiply _).reindex _

lemma orderedCutForm_core_antisymmetric {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) (b : Fin L → Fin 2) :
    CoreAntisymmetric (orderedCutForm p hp ψ b) := by
  have ha := (hψ.reindex (cutOrder b)).coreAntisymmetric.multiply
    (spatialProduct p hp (coreCutLabels (cutCoreNumber b) (cutOutNumber b)))
    (fun π x => spatialProduct_invariant p _ (corePerm _ π) (coreCutLabels_invariant π) x)
  intro π s
  simpa only [orderedCutForm_value] using ha π s

lemma orderedCutForm_mass {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) :
    formMass (orderedCutForm p hp ψ b) = formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) :=
  formMass_reindex _ _

lemma orderedCutForm_energy {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) (Z : ℝ) :
    formEnergy Z (orderedCutForm p hp ψ b) = formEnergy Z (multiplyForm (spatialProduct (N := L) p hp b) ψ) :=
  formEnergy_reindex _ _ _

def cutCoreEnergy {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (Z : ℝ) (ψ : FormVector L) (b : Fin L → Fin 2) : ℝ :=
  ∑ t : Spins (cutOutNumber b), ∫ y,
    formEnergy Z (coreSlice (orderedCutForm p hp ψ b) t y)

theorem cutCoreEnergy_priced {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) (b : Fin L → Fin 2)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam * formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) ≤
      cutCoreEnergy p hp Z ψ b + lam * cutCoreNumber b *
        formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) := by
  have hh := (orderedCutForm_core_antisymmetric p hp hψ b).integrated_priced
    (orderedCutForm_sobolev p hp hψ.sobolevVector b) hZ hlam
  simpa only [orderedCutForm_mass, cutCoreEnergy] using hh

theorem fock_cut_deletion {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) {Z lam ε : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hm : formMass ψ = 1)
    (he : formEnergy Z ψ + lam * L ≤ priceEnergy (energy Z) lam + ε) :
    (∑ b : (Fin L → Fin 2),
      (formEnergy Z (multiplyForm (spatialProduct (N := L) p hp b) ψ) - cutCoreEnergy p hp Z ψ b +
        lam * cutOutNumber b * formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ))) ≤
      ε + (1/2:ℝ) * weightedParticleCount ψ (spatialErrorWeight p) := by
  have hb (b : Fin L → Fin 2) := cutCoreEnergy_priced p hp hψ b hZ hlam
  have hmass := spatial_cut_mass p hp hψ.sobolevVector
  have henergy := spatial_cut_ims p hp hψ.sobolevVector Z
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hb b)
  have hcard (b : Fin L → Fin 2) : (cutCoreNumber b : ℝ) + cutOutNumber b = L := by
    exact_mod_cast cutNumbers_sum b
  have hid (b : Fin L → Fin 2) :
      lam * cutOutNumber b * formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) =
        lam * L * formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) -
          lam * cutCoreNumber b * formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) := by
    rw [← hcard b]; ring
  simp_rw [hid]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum ⊢
  rw [hm] at hmass
  rw [hmass, mul_one] at hsum ⊢
  rw [henergy]
  change _ ≤ ε + (1/2:ℝ) * weightedParticleCount ψ (spatialErrorWeight p)
  unfold weightedParticleCount
  linarith

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
