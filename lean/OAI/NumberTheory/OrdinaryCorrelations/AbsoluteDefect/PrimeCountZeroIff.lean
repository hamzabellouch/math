import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinnedRamareError
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeProductSquarefree

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

namespace OrdinaryCorrelations.SourcePrimeFactor
open Finset

lemma primeCount_zero_iff (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (n : ℕ) :
    primeCount P n=0 ↔ n.Coprime (∏p∈P,p) := by
  simp only [primeCount,Finset.card_eq_zero,filter_eq_empty_iff,Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    exact ((hP p hp).coprime_iff_not_dvd.mpr (h hp)).symm
  · intro h p hp
    exact (hP p hp).coprime_iff_not_dvd.mp (h p hp).symm

lemma multiples_Icc_card (N k : ℕ) : ((Icc 1 N).filter (fun n => k∣n)).card=N/k := by
  have he : (Icc 1 N).filter (fun n => k∣n)=
      (range (N+1)).filter (fun n => n≠0 ∧ k∣n) := by
    ext n
    simp only [mem_filter,mem_Icc,mem_range]
    omega
  rw [he]
  exact Nat.card_multiples' N k

lemma ramareArithmeticExceptions_card (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (L U : ℕ) :
    ((ramareArithmeticExceptions P L U).card:ℝ) ≤
      (((Icc 1 U).filter (fun n => n.Coprime (∏p∈P,p))).card:ℝ)+
        (U:ℝ)*(∑p∈P,(p:ℝ)⁻¹^2) := by
  classical
  let A := (Icc 1 U).filter (fun n => n.Coprime (∏p∈P,p))
  let B : ℕ → Finset ℕ := fun p => (Icc 1 U).filter (fun n => p^2∣n)
  have hsub : ramareArithmeticExceptions P L U ⊆ A ∪ P.biUnion B := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hn,hr|⟨p,hp,hd⟩⟩
    · apply mem_union_left
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,(mem_Ioc.mp hn).2⟩,
        (primeCount_zero_iff P hP n).mp hr⟩
    · apply mem_union_right
      exact mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨mem_Icc.mpr
        ⟨by have := (mem_Ioc.mp hn).1; omega,(mem_Ioc.mp hn).2⟩,hd⟩⟩
  have hc := (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le A.card))
  have hcr : ((ramareArithmeticExceptions P L U).card:ℝ)≤(A.card:ℝ)+∑p∈P,((B p).card:ℝ) := by exact_mod_cast hc
  apply hcr.trans
  change (A.card:ℝ)+_≤(A.card:ℝ)+_
  apply add_le_add_right
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  simp only [B,multiples_Icc_card]
  have hh := Nat.cast_div_le (α:=ℝ) (m:=U) (n:=p^2)
  simpa only [Nat.cast_pow,div_eq_mul_inv,inv_pow] using hh

theorem binnedRamare_arithmetic_energy (P : Finset ℕ) {Q : ℕ} (hQ : 0<Q)
    (hPQ : P⊆Q.primesLE) (M : ℕ → ℕ) {f : ℕ → ℂ}
    (hf : OneBounded f) (hm : Multiplicative f) (X E : ℕ)
    (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E) :
    (∑n∈Ioc (X-E) (2*(X+E)),‖binnedRamareError P M f X n‖^2) ≤
      4*(4*((X:ℝ)+E)*Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+(4*(Q:ℝ))^8+
        2*((X:ℝ)+E)*(∑p∈P,(p:ℝ)⁻¹^2)+6*(E:ℝ)) := by
  have hP : ∀p∈P,Nat.Prime p := fun p hp => Nat.prime_of_mem_primesLE (hPQ hp)
  have he := binnedRamareError_energy P hP M hf hm X E hrange
  have ha := ramareArithmeticExceptions_card P hP (X-E) (2*(X+E))
  have hr := OrdinaryWindowEuler.prime_window_rough P hQ hPQ (2*(X+E))
  push_cast at ha hr
  nlinarith

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
