import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.SobolevVector

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
namespace CoulombAtom

def sumForm {ι : Type*} [Fintype ι] {N : ℕ} (ψ : ι → FormVector N) : FormVector N where
  value s x := ∑ k, (ψ k).value s x
  gradient s i a x := ∑ k, (ψ k).gradient s i a x

lemma SobolevVector.sum {ι : Type*} [Fintype ι] {N : ℕ} {ψ : ι → FormVector N}
    (hψ : ∀ k, SobolevVector (ψ k)) : SobolevVector (sumForm ψ) := by
  classical
  refine ⟨fun s => memLp_finsetSum _ (fun k _ => (hψ k).1 s),
    fun s i a => memLp_finsetSum _ (fun k _ => (hψ k).2.1 s i a), ?_⟩
  intro s i a φ hφ hcφ
  change (∫ x, (∑ k, (ψ k).value s x) * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
    -(∫ x, (∑ k, (ψ k).gradient s i a x) * (φ x : ℂ))
  simp only [Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun k _ => show Integrable (fun x =>
      (ψ k).value s x * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) from
      ((hψ k).1 s).integrable_mul (test_deriv_memLp hφ hcφ (direction i a))),
    integral_finsetSum Finset.univ (fun k _ => show Integrable (fun x =>
      (ψ k).gradient s i a x * (φ x : ℂ)) from
      ((hψ k).2.1 s i a).integrable_mul (test_memLp hφ hcφ))]
  simp only [(hψ _).2.2 s i a φ hφ hcφ, Finset.sum_neg_distrib]

lemma SobolevVector.scale {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) (c : ℝ) :
    SobolevVector (scaleForm c ψ) := by
  refine ⟨fun s => (hψ.1 s).const_mul _, fun s i a => (hψ.2.1 s i a).const_mul _, ?_⟩
  intro s i a φ hφ hcφ
  change (∫ x, ((c : ℂ) * ψ.value s x) * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
    -(∫ x, ((c : ℂ) * ψ.gradient s i a x) * (φ x : ℂ))
  simp only [mul_assoc, integral_const_mul, hψ.2.2 s i a φ hφ hcφ, mul_neg]

lemma norm_sum_sq_disjoint {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (h : ∀ i j, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
  classical
  by_cases hz : ∀ i, v i = 0
  · simp [hz]
  · push Not at hz
    obtain ⟨i,hi⟩ := hz
    have hh (j : ι) (hji : j ≠ i) : v j = 0 := (h j i hji).resolve_right hi
    rw [Finset.sum_eq_single i (fun j _ hj => hh j hj) (by simp),
      Finset.sum_eq_single i (fun j _ hj => by simp [hh j hj]) (by simp)]

def FormsDisjoint {ι : Type*} {N : ℕ} (ψ : ι → FormVector N) : Prop :=
  (∀ k l, k ≠ l → ∀ s x, (ψ k).value s x = 0 ∨ (ψ l).value s x = 0) ∧
  (∀ k l, k ≠ l → ∀ s i a x,
    (ψ k).gradient s i a x = 0 ∨ (ψ l).gradient s i a x = 0)

lemma formMass_sum_disjoint {ι : Type*} [Fintype ι] {N : ℕ} {ψ : ι → FormVector N}
    (hψ : ∀ k, SobolevVector (ψ k)) (hd : FormsDisjoint ψ) :
    formMass (sumForm ψ) = ∑ k, formMass (ψ k) := by
  unfold formMass
  have hh (s : Spins N) : (∫ x, ‖(sumForm ψ).value s x‖^2) =
      ∑ k, ∫ x, ‖(ψ k).value s x‖^2 := by
    simp only [sumForm, norm_sum_sq_disjoint _ (fun k l hkl => hd.1 k l hkl s _)]
    exact integral_finsetSum _ (fun k _ => ((hψ k).1 s).norm.integrable_sq)
  simp_rw [hh]
  exact Finset.sum_comm

lemma formEnergy_sum_disjoint {ι : Type*} [Fintype ι] {N : ℕ} {ψ : ι → FormVector N}
    (hψ : ∀ k, SobolevVector (ψ k)) (hd : FormsDisjoint ψ) (Z : ℝ) :
    formEnergy Z (sumForm ψ) = ∑ k, formEnergy Z (ψ k) := by
  classical
  have hk (s : Spins N) (i : Fin N) (a : Fin 3) :
      (∫ x, ‖(sumForm ψ).gradient s i a x‖^2) = ∑ k, ∫ x, ‖(ψ k).gradient s i a x‖^2 := by
    simp only [sumForm, norm_sum_sq_disjoint _ (fun k l hkl => hd.2 k l hkl s i a _)]
    exact integral_finsetSum _ (fun k _ => ((hψ k).2.1 s i a).norm.integrable_sq)
  have hn (s : Spins N) (i : Fin N) :
      (∫ x, ‖(sumForm ψ).value s x‖^2 / ‖x i‖) =
      ∑ k, ∫ x, ‖(ψ k).value s x‖^2 / ‖x i‖ := by
    simp only [sumForm, norm_sum_sq_disjoint _ (fun k l hkl => hd.1 k l hkl s _), Finset.sum_div]
    exact integral_finsetSum _ (fun k _ => (hψ k).nuclear_integrable s i)
  have hp (s : Spins N) (i j : Fin N) :
      (if i < j then ∫ x, ‖(sumForm ψ).value s x‖^2 / ‖x i-x j‖ else 0) =
      ∑ k, if i < j then ∫ x, ‖(ψ k).value s x‖^2 / ‖x i-x j‖ else 0 := by
    by_cases hij : i < j
    · simp only [ite_eq_left hij, sumForm,
        norm_sum_sq_disjoint _ (fun k l hkl => hd.1 k l hkl s _), Finset.sum_div]
      exact integral_finsetSum _ (fun k _ => (hψ k).pair_integrable s i j hij.ne)
    · simp only [ite_eq_right hij, Finset.sum_const_zero]
  unfold formEnergy
  simp_rw [hk,hn,hp]
  rw [show (∑ s, ∑ i, ∑ a, ∑ k, ∫ x, ‖(ψ k).gradient s i a x‖^2) =
    ∑ k, ∑ s, ∑ i, ∑ a, ∫ x, ‖(ψ k).gradient s i a x‖^2 by
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun a k =>
        ∫ x, ‖(ψ k).gradient _ _ a x‖^2)]
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i k =>
        ∑ a, ∫ x, ‖(ψ k).gradient _ i a x‖^2)]
      exact Finset.sum_comm,
    show (∑ s, ∑ i, ∑ k, ∫ x, ‖(ψ k).value s x‖^2 / ‖x i‖) =
    ∑ k, ∑ s, ∑ i, ∫ x, ‖(ψ k).value s x‖^2 / ‖x i‖ by
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i k =>
        ∫ x, ‖(ψ k).value _ x‖^2 / ‖x i‖)]
      exact Finset.sum_comm,
    show (∑ s, ∑ i, ∑ j, ∑ k, if i < j then ∫ x, ‖(ψ k).value s x‖^2 / ‖x i-x j‖ else 0) =
    ∑ k, ∑ s, ∑ i, ∑ j, if i < j then ∫ x, ‖(ψ k).value s x‖^2 / ‖x i-x j‖ else 0 by
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun j k =>
        if _ < j then ∫ x, ‖(ψ k).value _ x‖^2 / ‖x _-x j‖ else 0)]
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i k =>
        ∑ j, if i < j then ∫ x, ‖(ψ k).value _ x‖^2 / ‖x i-x j‖ else 0)]
      exact Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

end CoulombAtom

open MeasureTheory Filter
open scoped BigOperators

end

end OAI
