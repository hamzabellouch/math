import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CutCoreNumber
import OAI.Analysis.CoulombIonization.Ionization.InsertionTermsDisjointSet

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
namespace CoulombAtom

lemma spatialProduct_zero_of_factor {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (b : Fin L → Fin 2) (x : Configuration L) (j : Fin L)
    (hv : (p (b j)).value (x j) = 0) : spatialProductValue p b x = 0 := by
  classical
  exact Finset.prod_eq_zero (Finset.mem_univ j) hv

lemma spatialProduct_derivative_zero_of_factor {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (b : Fin L → Fin 2) (x : Configuration L) (j : Fin L)
    (hv : (p (b j)).value (x j) = 0)
    (hd : ∀ a, lineDeriv ℝ (p (b j)).value (x j) (spaceDirections a) = 0)
    (i : Fin L) (a : Fin 3) :
    lineDeriv ℝ (spatialProductValue p b) x (direction i a) = 0 := by
  classical
  rw [spatialProduct_derivative]
  by_cases hij : j = i
  · subst i
    rw [hd,mul_zero]
  · rw [show (∏ k ∈ Finset.univ.erase i, (p (b k)).value (x k)) = 0 from
        Finset.prod_eq_zero (by simp [hij]) hv,zero_mul]

lemma multiplyForm_spatial_zero_of_factor {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) (x : Configuration L) (j : Fin L)
    (hv : (p (b j)).value (x j) = 0)
    (hd : ∀ a, lineDeriv ℝ (p (b j)).value (x j) (spaceDirections a) = 0) :
    FormZeroAt (multiplyForm (spatialProduct p hp b) ψ) x := by
  have hval := spatialProduct_zero_of_factor p b x j hv
  have hg := spatialProduct_derivative_zero_of_factor p b x j hv hd
  intro s
  constructor
  · change (spatialProductValue p b x : ℂ) * _ = 0
    rw [hval,Complex.ofReal_zero,zero_mul]
  · intro i a
    change (spatialProductValue p b x : ℂ) * _ +
      Complex.ofReal (lineDeriv ℝ (spatialProductValue p b) x (direction i a)) * _ = 0
    rw [hval,hg,Complex.ofReal_zero,zero_mul,zero_mul,add_zero]

lemma FormZeroAt.reindex {N M : ℕ} {ψ : FormVector N} (e : Fin M ≃ Fin N)
    {x : Configuration M} (h : FormZeroAt ψ (x ∘ e.symm)) :
    FormZeroAt (reindexForm e ψ) x := by
  intro s
  exact ⟨(h (s ∘ e.symm)).1,fun i a => (h (s ∘ e.symm)).2 (e i) a⟩

lemma FormZeroAt.coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    {x : Configuration N} {y : Configuration M}
    (h : FormZeroAt ψ (joinLists x y)) (t : Spins M) :
    FormZeroAt (coreSlice ψ t y) x := by
  intro s
  exact ⟨(h (joinLists s t)).1,fun i a => (h (joinLists s t)).2 (finSumFinEquiv (Sum.inl i)) a⟩

lemma orderedCutForm_core_hole {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) (S : Set Space)
    (hv : ∀ x ∈ S, (p 0).value x = 0)
    (hd : ∀ x ∈ S, ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    (x : Configuration (cutCoreNumber b + cutOutNumber b)) (i : Fin (cutCoreNumber b))
    (hi : x (finSumFinEquiv (Sum.inl i)) ∈ S) :
    FormZeroAt (orderedCutForm p hp ψ b) x := by
  let j : Fin (cutCoreNumber b + cutOutNumber b) := finSumFinEquiv (Sum.inl i)
  have hj : b (cutOrder b j) = 0 := by
    have hh := congrFun (cutOrder_labels b) j
    simpa only [Function.comp_apply,j,coreCutLabels,joinLists_left] using hh
  apply FormZeroAt.reindex
  apply multiplyForm_spatial_zero_of_factor p hp ψ b _ (cutOrder b j)
  · simpa only [Function.comp_apply,Equiv.symm_apply_apply,hj] using hv (x j) hi
  · intro a
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,hj] using hd (x j) hi a

theorem cut_core_local_insertion {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) (b : Fin L → Fin 2)
    (S : Set Space)
    (hv : ∀ x ∈ S, (p 0).value x = 0)
    (hd : ∀ x ∈ S, ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {φ : FormVector 1} (hφ : FormAdmissible φ)
    (he : ∀ x, x 0 ∉ S → FormZeroAt φ x)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) (t : Spins (cutOutNumber b)) :
    ∀ᵐ y, let q := coreSlice (orderedCutForm p hp ψ b) t y
      Z * formMass q * formNuclear φ - tensorCross q φ ≤
        (formEnergy Z q + lam*cutCoreNumber b*formMass q -
          priceEnergy (energy Z) lam * formMass q) + formMass q * (formKinetic φ+lam) := by
  apply ((orderedCutForm_core_antisymmetric p hp hψ b).ae_coreSlice
    (orderedCutForm_sobolev p hp hψ.sobolevVector b) t).mono
  intro y hy
  apply local_screened_insertion hy hφ S _ he hZ hlam
  intro x i hi
  exact (orderedCutForm_core_hole p hp ψ b S hv hd (joinLists x y) i
    (by simpa only [joinLists_left] using hi)).coreSlice t

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
