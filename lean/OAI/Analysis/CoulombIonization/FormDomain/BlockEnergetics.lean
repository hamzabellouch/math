import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoreKinetic

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

def outKinetic {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  (1/2:ℝ)*∑ s, ∑ i : Fin M, ∑ a, ∫ z, ‖ψ.gradient s (finSumFinEquiv (Sum.inr i)) a z‖^2

def outRepulsion {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin M, ∑ j : Fin M, if i < j then
    ∫ z, ‖ψ.value s z‖^2/‖z (finSumFinEquiv (Sum.inr i))-z (finSumFinEquiv (Sum.inr j))‖ else 0

def crossRepulsion {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin N, ∑ j : Fin M,
    ∫ z, ‖ψ.value s z‖^2/‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖

lemma formKinetic_core_out {N M : ℕ} (ψ : FormVector (N+M)) :
    formKinetic ψ = coreKinetic ψ+outKinetic ψ := by
  unfold formKinetic coreKinetic outKinetic
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]

lemma finite_pair_core_out_cross {N M : ℕ} (f : Fin (N+M) → Fin (N+M) → ℝ) :
    (∑ i : Fin (N+M), ∑ j : Fin (N+M), if i < j then f i j else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then f (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) else 0)+
      (∑ i : Fin M, ∑ j : Fin M, if i < j then f (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) else 0)+
      ∑ i : Fin N, ∑ j : Fin M, f (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) := by
  have hl (i j : Fin N) : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) < finSumFinEquiv (Sum.inl j) ↔ i < j := Iff.rfl
  have hr (i j : Fin M) : (finSumFinEquiv (Sum.inr i) : Fin (N+M)) < finSumFinEquiv (Sum.inr j) ↔ i < j := by
    change N+i.val < N+j.val ↔ i.val < j.val
    omega
  have hlr (i : Fin N) (j : Fin M) : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) < finSumFinEquiv (Sum.inr j) := by
    change i.val < N+j.val
    omega
  have hrl (i : Fin M) (j : Fin N) : ¬ (finSumFinEquiv (Sum.inr i) : Fin (N+M)) < finSumFinEquiv (Sum.inl j) := by
    change ¬ N+i.val < j.val
    omega
  rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  have he (i : Fin (N+M)) : (∑ j : Fin (N+M), if i < j then f i j else 0) =
      (∑ j : Fin N, if i < finSumFinEquiv (Sum.inl j) then f i (finSumFinEquiv (Sum.inl j)) else 0)+
      ∑ j : Fin M, if i < finSumFinEquiv (Sum.inr j) then f i (finSumFinEquiv (Sum.inr j)) else 0 := by
    rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  simp_rw [he]
  simp only [hl,hr,hlr,hrl,ite_true,ite_false,Finset.sum_const_zero,zero_add,Finset.sum_add_distrib]
  ring

lemma formRepulsion_core_out_cross {N M : ℕ} (ψ : FormVector (N+M)) :
    formRepulsion ψ = coreRepulsion ψ+outRepulsion ψ+crossRepulsion ψ := by
  unfold formRepulsion coreRepulsion outRepulsion crossRepulsion
  simp_rw [finite_pair_core_out_cross]
  simp only [Finset.sum_add_distrib]

theorem formEnergy_core_out_cross {N M : ℕ} (Z : ℝ) (ψ : FormVector (N+M)) :
    formEnergy Z ψ = (coreKinetic ψ-Z*coreNuclear ψ+coreRepulsion ψ)+
      outKinetic ψ-Z*outNuclear ψ+outRepulsion ψ+crossRepulsion ψ := by
  rw [formEnergy_parts,formKinetic_core_out,formNuclear_core_out,formRepulsion_core_out_cross]
  ring

end CoulombAtom

end

end OAI
