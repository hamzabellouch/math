import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCountRoughZero
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ActualMassOne

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
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothRough
open Finset OrdinarySelbergWeights OrdinaryCorrelations

def cofactorEnergy (f : ℕ → ℂ) (P S : Finset ℕ) (T : Finset ℝ) : ℝ :=
  ∑ t ∈ T, ‖∑ n ∈ S, cofactorTerm f P n t‖^2

lemma cofactor_coefficient_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (P : Finset ℕ) (n : ℕ) : ‖f n / (SourcePrimeFactor.primeCount P n + 1:ℂ)‖ ≤ 1 := by
  rw [norm_div]
  have he : ‖(SourcePrimeFactor.primeCount P n + 1:ℂ)‖ =
      (SourcePrimeFactor.primeCount P n:ℝ)+1 := by
    norm_cast
  rw [he]
  apply (div_le_one (by positivity)).mpr
  exact (hf n).trans (by linarith [Nat.cast_nonneg (α:=ℝ) (SourcePrimeFactor.primeCount P n)])

lemma complex_norm_add_sq (a b : ℂ) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg (a+b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖-‖b‖)]

lemma cofactorEnergy_union (f : ℕ → ℂ) (P A B : Finset ℕ) (T : Finset ℝ)
    (hd : Disjoint A B) :
    cofactorEnergy f P (A∪B) T ≤ 2*cofactorEnergy f P A T + 2*cofactorEnergy f P B T := by
  unfold cofactorEnergy
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro t ht
  rw [sum_union hd]
  exact complex_norm_add_sq _ _

lemma cofactorEnergy_biUnion {ι : Type*} [DecidableEq ι]
    (f : ℕ → ℂ) (P : Finset ℕ) (I : Finset ι) (C : ι → Finset ℕ) (T : Finset ℝ)
    (hd : (I : Set ι).PairwiseDisjoint C) :
    cofactorEnergy f P (I.biUnion C) T ≤ (I.card:ℝ)*∑ i ∈ I, cofactorEnergy f P (C i) T := by
  unfold cofactorEnergy
  rw [← sum_comm, mul_sum]
  apply sum_le_sum
  intro t ht
  rw [sum_biUnion hd]
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
  exact sq_sum_le_card_mul_sum_sq

theorem sparse_cofactor_decomposition {ι : Type*} [DecidableEq ι]
    {f : ℕ → ℂ} (hf : OneBounded f) (P S : Finset ℕ)
    (I : Finset ι) (C : ι → Finset ℕ) (T : Finset ℝ)
    (u B : ℕ) (hu : 1 ≤ u) (hB : 0<B) (hBU : B ≤ u^8)
    (hS : S ⊆ Icc (2*B) (4*B))
    (hC : ∀ i ∈ I, C i ⊆ S) (hd : (I : Set ι).PairwiseDisjoint C)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u:ℝ)^10) :
    cofactorEnergy f P S T ≤
      2*(I.card:ℝ)*(∑ i ∈ I, cofactorEnergy f P (C i) T) +
      2*(264+3200*(T.card:ℝ)*(u:ℝ)^7/B)*((S\I.biUnion C).card:ℝ)/(4*(B:ℝ)) := by
  have hsub : I.biUnion C ⊆ S := biUnion_subset.mpr hC
  have heq : S = I.biUnion C ∪ (S\I.biUnion C) := (union_sdiff_of_subset hsub).symm
  have hsplit := cofactorEnergy_union f P (I.biUnion C) (S\I.biUnion C) T disjoint_sdiff_self_right
  rw [← heq] at hsplit
  have hmid := cofactorEnergy_biUnion f P I C T hd
  have herr := sparse_harmonic_density (S\I.biUnion C) T
    (fun n => f n / (SourcePrimeFactor.primeCount P n+1:ℂ)) u B hu hB hBU
    (fun n hn => hS (mem_sdiff.mp hn).1)
    (fun n _ => cofactor_coefficient_bound hf P n) hsep hheight
  change cofactorEnergy f P (S\I.biUnion C) T ≤ _ at herr
  calc
    _ ≤ 2*((I.card:ℝ)*(∑ i ∈ I, cofactorEnergy f P (C i) T)) +
        2*((264+3200*(T.card:ℝ)*(u:ℝ)^7/B)*((S\I.biUnion C).card:ℝ)/(4*(B:ℝ))) := by linarith
    _ = _ := by ring

end OrdinarySmoothRough

end

end OAI
