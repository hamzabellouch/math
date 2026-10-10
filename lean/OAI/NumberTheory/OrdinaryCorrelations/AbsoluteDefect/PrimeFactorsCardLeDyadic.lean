import Mathlib

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
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryMellinModulus
open Finset

lemma primeFactors_card_le_dyadic {d s : ℕ} (hd : 0<d) (hs : d ≤ 2^s) :
    d.primeFactors.card ≤ s/4+16 := by
  let P := d.primeFactors.filter (fun p=>16 ≤ p)
  let R := d.primeFactors.filter (fun p=>p<16)
  have hP : P ⊆ d.primeFactors := filter_subset _ _
  have hR : R ⊆ range 16 := by
    intro p hp
    exact mem_range.mpr (mem_filter.mp hp).2
  have hcard : d.primeFactors.card=P.card+R.card := by
    have he : P∪R=d.primeFactors := by
      ext p
      simp only [P,R,Finset.mem_union,Finset.mem_filter]
      by_cases hp : p∈d.primeFactors
      · simp only [hp,true_and,iff_true]
        omega
      · simp [hp]
    have hdj : Disjoint P R := by
      apply Finset.disjoint_left.mpr
      intro p hp hr
      have := (mem_filter.mp hp).2
      have := (mem_filter.mp hr).2
      omega
    rw [←he,card_union_of_disjoint hdj]
  have hpow : 16^P.card ≤ d := by
    calc
      _ = ∏_p∈P,(16:ℕ) := by simp
      _  ≤  ∏p∈P,p := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun p hp => (mem_filter.mp hp).2)
      _  ≤  d := Nat.le_of_dvd hd ((prod_dvd_prod_of_subset P d.primeFactors id hP).trans
        (Nat.prod_primeFactors_dvd d))
  have hpow' : (2:ℕ)^(4*P.card) ≤ 2^s := by
    have he : (2:ℕ)^(4*P.card)=16^P.card := by rw [pow_mul]; norm_num
    rw [he]
    exact hpow.trans hs
  have hbig : 4*P.card ≤ s := (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hpow'
  have hr := Finset.card_le_card hR
  simp only [card_range] at hr
  omega

lemma primeFactors_card_le_five_mul {d m : ℕ} (hd : 0<d) (hs : d ≤ 2^(5*m)) :
    d.primeFactors.card ≤ 2*m+16 := by
  have ht := primeFactors_card_le_dyadic hd hs
  omega

end OrdinaryMellinModulus

end

end OAI
