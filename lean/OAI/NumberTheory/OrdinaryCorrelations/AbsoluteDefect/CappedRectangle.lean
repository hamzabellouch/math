import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CapUpper

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory
open MeasureTheory Complex
open Finset Filter

namespace OrdinarySmoothRough
open Finset OrdinarySelbergWeights

def cappedRectangle (S : Finset ℕ) (N A B : ℕ) : Finset ℕ :=
  cutRectangle S N A B (capUpper N A B)

lemma cappedRectangle_subset_slice (S : Finset ℕ) (N A B : ℕ) (hA : 0<A) :
    cappedRectangle S N A B ⊆ smoothSlice S N A B :=
  (cutRectangle_subset _ _ _ _ _ (min_le_left _ _)).trans (rectangle_subset_slice S N A B hA)

lemma slice_disjoint (S : Finset ℕ) (N A B C D : ℕ)
    (hd : Disjoint (Ioc A B) (Ioc C D)) :
    Disjoint (smoothSlice S N A B) (smoothSlice S N C D) := by
  apply disjoint_left.mpr
  intro n hn hm
  have h1 := (mem_filter.mp hn).2
  have h2 := (mem_filter.mp hm).2
  exact disjoint_left.mp hd (mem_Ioc.mpr h1) (mem_Ioc.mpr h2)

lemma cappedRectangle_disjoint (S : Finset ℕ) (N A B C D : ℕ)
    (hA : 0<A) (hC : 0<C) (hd : Disjoint (Ioc A B) (Ioc C D)) :
    Disjoint (cappedRectangle S N A B) (cappedRectangle S N C D) :=
  (slice_disjoint S N A B C D hd).mono
    (cappedRectangle_subset_slice S N A B hA) (cappedRectangle_subset_slice S N C D hC)

lemma rectangle_union_remainder {ι : Type*} [DecidableEq ι]
    (S : Finset ℕ) (N L U : ℕ) (I : Finset ι) (A B : ι → ℕ)
    (hcover : ∀ a : ℕ, L<a → a≤U → ∃ i∈I, A i<a ∧ a≤B i) :
    (Ioc N (2*N)) \ (I.biUnion (fun i => cappedRectangle S N (A i) (B i))) ⊆
      ((Icc 1 (2*N)).filter (fun n => smoothPart S n ≤ L)) ∪
      ((Icc 1 (2*N)).filter (fun n => U < smoothPart S n)) ∪
      I.biUnion (fun i => smoothSlice S N (A i) (B i) \ cappedRectangle S N (A i) (B i)) := by
  intro n hn
  obtain ⟨hnI,hnR⟩ := mem_sdiff.mp hn
  have hnPos : n ∈ Icc 1 (2*N) := by
    have hh := mem_Ioc.mp hnI
    exact mem_Icc.mpr ⟨by omega, hh.2⟩
  by_cases hL : smoothPart S n ≤ L
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnPos,hL⟩))
  by_cases hU : U < smoothPart S n
  · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnPos,hU⟩))
  obtain ⟨i,hi,hAi,hBi⟩ := hcover (smoothPart S n) (by omega) (by omega)
  apply mem_union_right
  apply mem_biUnion.mpr
  refine ⟨i,hi,mem_sdiff.mpr ⟨mem_filter.mpr ⟨hnI,hAi,hBi⟩,?_⟩⟩
  intro h
  exact hnR (mem_biUnion.mpr ⟨i,hi,h⟩)

lemma rectangle_union_remainder_card {ι : Type*} [DecidableEq ι]
    (S : Finset ℕ) (N L U : ℕ) (I : Finset ι) (A B : ι → ℕ)
    (hcover : ∀ a : ℕ, L<a → a≤U → ∃ i∈I, A i<a ∧ a≤B i) :
    ((Ioc N (2*N)) \ (I.biUnion (fun i => cappedRectangle S N (A i) (B i)))).card ≤
      ((Icc 1 (2*N)).filter (fun n => smoothPart S n ≤ L)).card +
      ((Icc 1 (2*N)).filter (fun n => U < smoothPart S n)).card +
      ∑ i ∈ I, (smoothSlice S N (A i) (B i) \ cappedRectangle S N (A i) (B i)).card := by
  apply (card_le_card (rectangle_union_remainder S N L U I A B hcover)).trans
  exact (card_union_le _ _).trans
    (Nat.add_le_add (card_union_le _ _) (card_biUnion_le))

theorem capped_family_remainder_sieve {ι : Type*} [DecidableEq ι]
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (N L U z : ℕ) (I : Finset ι) (A B : ι → ℕ)
    (hcover : ∀ a : ℕ, L<a → a≤U → ∃ i∈I, A i<a ∧ a≤B i)
    (hA : ∀ i∈I, 0<A i) (hAB : ∀ i∈I, A i≤B i)
    (hz : 1≤z) (hprime : Squarefree (∏ p ∈ S,p)) :
    (((Ioc N (2*N)) \ (I.biUnion (fun i => cappedRectangle S N (A i) (B i)))).card:ℝ) ≤
      (((Icc 1 (2*N)).filter (fun n => smoothPart S n ≤ L)).card:ℝ) +
      (((Icc 1 (2*N)).filter (fun n => U < smoothPart S n)).card:ℝ) +
      ∑ i∈I, ((B i:ℝ)-(A i:ℝ)) *
        ((3*(N:ℝ)*((B i:ℝ)-(A i:ℝ))/((A i:ℝ)*(B i:ℝ)) + 8) *
          (actualMass (∏ p ∈ S,p) z hprime)⁻¹ + 4*(z:ℝ)^4) := by
  have hc : (((Ioc N (2*N)) \ (I.biUnion (fun i => cappedRectangle S N (A i) (B i)))).card:ℝ) ≤
      (((Icc 1 (2*N)).filter (fun n => smoothPart S n ≤ L)).card:ℝ) +
      (((Icc 1 (2*N)).filter (fun n => U < smoothPart S n)).card:ℝ) +
      ∑ i∈I, ((smoothSlice S N (A i) (B i) \ cappedRectangle S N (A i) (B i)).card:ℝ) := by
    exact_mod_cast rectangle_union_remainder_card S N L U I A B hcover
  apply hc.trans
  apply _root_.add_le_add le_rfl
  apply sum_le_sum
  intro i hi
  exact capped_slice_defect_sieve S hS N (A i) (B i) z (hA i hi) (hAB i hi) hz hprime

end OrdinarySmoothRough

end

end OAI
