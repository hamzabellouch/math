import OAI.NumberTheory.TotientAsymptotic.PrimeFactorBands
import OAI.NumberTheory.TotientAsymptotic.CommonPrimeMass

namespace OAI

/-! Multiplicative and nested-truncation identities for actual collision bands. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBetween_support (n : ℕ) (U V : ℝ) {p : ℕ}
    (hp : p ∈ (partBetween n U V).primeFactorsList) : U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
  have hm := (partBetween_factors n U V).mem_iff.mpr hp
  exact of_decide_eq_true (List.mem_filter.mp hm).2

lemma partBetween_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s,f i ≠ 0) (U V : ℝ) :
    partBetween (∏ i ∈ s,f i) U V=∏ i ∈ s,partBetween (f i) U V := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [partBetween]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,
      partBetween_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma partBetween_eq_one_of_largest_le {n : ℕ} {U V : ℝ}
    (hn : (largestPrimeFactor n:ℝ) ≤ U) : partBetween n U V=1 := by
  have he := omegaIn_eq_zero_of_largest_le (T:=V) hn
  have hl : (n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V))=[] :=
    List.length_eq_zero_iff.mp he
  simp only [partBetween,hl,List.prod_nil]

lemma partBelow_all_of_largest_le {n : ℕ} {V : ℝ} (hn : n ≠ 0)
    (hV : (largestPrimeFactor n:ℝ) ≤ V) : partBelow n V=n := by
  have hall : n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)=n.primeFactorsList := by
    apply List.filter_eq_self.mpr
    intro p hp
    exact decide_eq_true ((show (p:ℝ) ≤ largestPrimeFactor n by
      exact_mod_cast primeFactor_le_largest hp).trans hV)
  simp only [partBelow,hall,Nat.prod_primeFactorsList hn]

lemma partBelow_nested (n : ℕ) {U V : ℝ} (hUV : U ≤ V) :
    partBelow (partBelow n V) U=partBelow n U := by
  have he := ((partBelow_factors n V).filter (fun p : ℕ => decide ((p:ℝ) ≤ U))).prod_eq
  have hf : (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).filter
      (fun p : ℕ => (p:ℝ) ≤ U)=n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ U) := by
    simp only [List.filter_filter]
    congr 1
    funext p
    by_cases h : (p:ℝ) ≤ U
    · simp [h,h.trans hUV]
    · simp [h]
  simpa only [hf,partBelow] using he.symm

lemma partBetween_below (n : ℕ) {U V W : ℝ} (hVW : V ≤ W) :
    partBetween (partBelow n W) U V=partBetween n U V := by
  have he := ((partBelow_factors n W).filter
    (fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ V))).prod_eq
  have hf : (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ W)).filter
      (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)=
      n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V) := by
    simp only [List.filter_filter]
    congr 1
    funext p
    by_cases h : U < (p:ℝ) ∧ (p:ℝ) ≤ V
    · simp [h,h.2.trans hVW]
    · simp only [decide_eq_false_iff_not.mpr h,Bool.false_and]
  simpa only [hf,partBetween] using he.symm

lemma common_band_product {k D e : ℕ} (f : PairedFactors k) {U V : ℝ}
    (hD : D ≠ 0) (he : e ≠ 0) (hl : ∀ i,f.1 i ≠ 0) (hr : ∀ i,f.2 i ≠ 0)
    (hprod : D*pairedProduct f=e*(∏ i,f.2 i))
    (hDs : (largestPrimeFactor D:ℝ) ≤ U) (hes : (largestPrimeFactor e:ℝ) ≤ U) :
    (∏ i,partBetween (f.1 i) U V)=∏ i,partBetween (f.2 i) U V := by
  have hh := congrArg (fun n => partBetween n U V) hprod
  unfold pairedProduct at hh
  rw [partBetween_mul hD (Finset.prod_ne_zero_iff.mpr (fun i _ => hl i)),
    partBetween_mul he (Finset.prod_ne_zero_iff.mpr (fun i _ => hr i)),
    partBetween_eq_one_of_largest_le hDs,partBetween_eq_one_of_largest_le hes,
    one_mul,one_mul,partBetween_prod _ _ (fun i _ => hl i),
    partBetween_prod _ _ (fun i _ => hr i)] at hh
  exact hh

end TotientAsymptotic

end

end OAI
