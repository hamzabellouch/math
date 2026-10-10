import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparsePreparedProbability
import OAI.Combinatorics.KMedian.Sparse.SparseRealExpectation

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

theorem outer_expectation (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (v : State n m → ℝ) :
    (law D c q Δ P y p hc hq).expectation (fun zG => v zG.1)=
      (SparseOuterLaw.law D c q hc hq).expectation v := by
  rw [law,SparseIntegerLaw.expectation_bindIndexed]
  simp only [kernel,SparseIntegerLaw.expectation_map,SparseIntegerLaw.expectation_const]
  rfl

theorem kernel_mean (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j) (hm : ∀ j,∑ i∈P j,y i=p j)
    (z : State n m) (i : Fin f) (j : Fin n) :
    (kernel D q Δ P y p z).moment (fun zG => (zG.2 j i:ℚ))=
      SparseRescaledInner.piece P y p (total D q Δ z) i j := by
  rw [kernel,SparseIntegerLaw.map_moment]
  exact SparseRescaledInner.mean P y p _ hy hp hm i j

theorem kernel_pair (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j) (hm : ∀ j,∑ i∈P j,y i=p j)
    (z : State n m) (i h : Fin f) (j k : Fin n) (hh : i≠h ∨ j≠k) :
    (kernel D q Δ P y p z).moment (fun zG => (zG.2 j i:ℚ)*(zG.2 k h:ℚ)) ≤
      SparseRescaledInner.piece P y p (total D q Δ z) i j*
        SparseRescaledInner.piece P y p (total D q Δ z) h k := by
  rw [kernel,SparseIntegerLaw.map_moment]
  exact SparseRescaledInner.pair P y p _ hy hp hm i h j k hh

theorem mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e)
    (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j) (hm : ∀ j,∑ i∈P j,y i=p j)
    (i : Fin f) (j : Fin n) :
    (law D c q Δ P y p hc hq).moment (fun zG => (zG.2 j i:ℚ))=
      (SparseOuterLaw.law D c q hc hq).moment (fun z =>
        SparseRescaledInner.piece P y p (total D q Δ z) i j) := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_mean D q Δ P y p hy hp hm]
  rfl

theorem pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e)
    (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j) (hm : ∀ j,∑ i∈P j,y i=p j)
    (i h : Fin f) (j k : Fin n) (hh : i≠h ∨ j≠k) :
    (law D c q Δ P y p hc hq).moment (fun zG => (zG.2 j i:ℚ)*(zG.2 k h:ℚ)) ≤
      (SparseOuterLaw.law D c q hc hq).moment (fun z =>
        SparseRescaledInner.piece P y p (total D q Δ z) i j*
          SparseRescaledInner.piece P y p (total D q Δ z) h k) := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  apply sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left (kernel_pair D q Δ P y p hy hp hm _ i h j k hh)
  exact (SparseOuterLaw.law D c q hc hq).law.rational.nonneg a

theorem joint_opening_probability (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (g : ℚ)
    (δ : Fin n → ℝ) {γ B : ℝ} (hg : 0 < g) (hγ : 0 < γ)
    (heven : Even Δ) (hunit : g*(Δ:ℚ)=1) (hδ : ∀ j,0 ≤ δ j)
    (hmean : ∀ j,(g:ℝ)*(targetMean D q j:ℝ)=(1+γ)*δ j)
    (hsmall : ∀ j,(1+γ)*δ j ≤ 1/4)
    (hplan : (g:ℝ)*(((n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e):ℚ):ℝ)=
      B-γ*∑ j,δ j) :
    1-4*(g:ℝ)*(1+γ)/γ ≤ (law D c q Δ P y p hc hq).realIndex.prob (fun a =>
      (g:ℝ)*(opening D c q Δ (law D c q Δ P y p hc hq).states[a.val].1:ℝ) ≤ B+3*(g:ℝ)) := by
  classical
  have hh := opening_probability D c q Δ hc hq g δ hg hγ heven hunit hδ hmean hsmall hplan
  change _ ≤ (law D c q Δ P y p hc hq).expectation
    (fun zG => if (g:ℝ)*(opening D c q Δ zG.1:ℝ) ≤ B+3*(g:ℝ) then 1 else 0)
  rw [outer_expectation D c q Δ P y p hc hq
    (fun z => if (g:ℝ)*(opening D c q Δ z:ℝ) ≤ B+3*(g:ℝ) then 1 else 0)]
  exact hh

end MetricKMedian.SparsePrepared
end
end

end OAI
