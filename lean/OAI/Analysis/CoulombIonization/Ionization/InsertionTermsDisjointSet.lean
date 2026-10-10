import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Form

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
namespace CoulombAtom

lemma insertionTerms_disjoint_set {N : ℕ} {T : FormVector (N+1)} (S : Set Space)
    (hc : ∀ x (j : Fin N), x j.castSucc ∈ S → FormZeroAt T x)
    (he : ∀ x, x (Fin.last N) ∉ S → FormZeroAt T x) :
    FormsDisjoint (insertionTerm T) := by
  have hh (k l : Fin (N+1)) (hkl : k ≠ l) (x : Configuration (N+1)) :
      FormZeroAt (insertionTerm T k) x ∨ FormZeroAt (insertionTerm T l) x := by
    by_cases hk : x k ∈ S
    · right
      have hne : insertionSwap l k ≠ Fin.last N := by
        intro h
        have ht := congrArg (insertionSwap l) h
        exact hkl (by simpa only [insertionSwap,Equiv.swap_apply_self,Equiv.swap_apply_right] using ht)
      obtain ⟨j,hj⟩ := Fin.exists_castSucc_eq.mpr hne
      apply insertionTerm_zero l
      apply hc _ j
      simpa only [Function.comp_apply,hj,insertionSwap,Equiv.swap_apply_self] using hk
    · left
      exact insertionTerm_zero k (he _ (by simpa only [Function.comp_apply,insertionSwap_last] using hk))
  constructor
  · intro k l hkl s x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl (hk s).1
    · exact Or.inr (hl s).1
  · intro k l hkl s i a x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl ((hk s).2 i a)
    · exact Or.inr ((hl s).2 i a)

lemma tensor_insertion_disjoint_set {N : ℕ} (ψ : FormVector N) (φ : FormVector 1)
    (S : Set Space)
    (hc : ∀ x i, x i ∈ S → FormZeroAt ψ x)
    (he : ∀ x, x 0 ∉ S → FormZeroAt φ x) :
    FormsDisjoint (insertionTerm (tensorForm ψ φ)) := by
  apply insertionTerms_disjoint_set S
  · intro x i hx
    exact tensor_zero_left ψ φ (hc _ i hx)
  · intro x hx
    exact tensor_zero_right ψ φ (he _ hx)

theorem local_insertion_priced_bound {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevFermion ψ) (hφ : FormAdmissible φ) (S : Set Space)
    (hc : ∀ x i, x i ∈ S → FormZeroAt ψ x)
    (he : ∀ x, x 0 ∉ S → FormZeroAt φ x) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam * formMass ψ ≤ formEnergy Z ψ +
      formMass ψ * (formKinetic φ - Z*formNuclear φ) + tensorCross ψ φ +
      lam * (N+1) * formMass ψ := by
  let T := tensorForm ψ φ
  have hT := hψ.sobolevVector.tensor hφ.sobolevFermion.sobolevVector
  have hd := tensor_insertion_disjoint_set ψ φ S hc he
  have hw := (wedgeForm_fermion hT (tensor_coreAntisymmetric hψ φ)).priced_lower_bound hZ hlam
  have hm : formMass φ = 1 := hφ.2.2.2.2.1
  rw [formMass_wedge hT hd,formEnergy_wedge hT hd,formMass_tensor,
    formEnergy_tensor_one,hm,mul_one,mul_one,Nat.cast_add,Nat.cast_one] at hw
  have hh : 0 < (N:ℝ)+1 := by positivity
  nlinarith

theorem local_screened_insertion {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevFermion ψ) (hφ : FormAdmissible φ) (S : Set Space)
    (hc : ∀ x i, x i ∈ S → FormZeroAt ψ x)
    (he : ∀ x, x 0 ∉ S → FormZeroAt φ x) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    Z * formMass ψ * formNuclear φ - tensorCross ψ φ ≤
      (formEnergy Z ψ + lam*N*formMass ψ - priceEnergy (energy Z) lam * formMass ψ) +
      formMass ψ * (formKinetic φ + lam) := by
  have hh := local_insertion_priced_bound hψ hφ S hc he hZ hlam
  nlinarith

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
