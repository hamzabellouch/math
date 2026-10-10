import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Phase
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Poly

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

namespace OrdinaryCorrelations.SourcePrimeFactor
open Finset OrdinaryDirichletMeanSquare

lemma bin_sum_by_multiples {p : ℕ} (hp : 0 < p) (M U : ℕ) (hU : p*(2*M)≤U)
    (g : ℕ → ℕ → ℂ) :
    (∑n∈Ioc 0 U,if p∣n ∧ n/p∈Finset.Ioc M (2*M) then g n (n/p) else 0)=
      ∑m∈Ioc M (2*M),g (p*m) m := by
  classical
  rw [←sum_filter]
  symm
  refine sum_bij (fun m _ => p*m) ?_ ?_ ?_ ?_
  · intro m hm
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_,?_⟩,dvd_mul_right p m,?_⟩
    · exact Nat.mul_pos hp (by have := (mem_Ioc.mp hm).1; omega)
    · exact (Nat.mul_le_mul_left p (mem_Ioc.mp hm).2).trans hU
    · simpa only [Nat.mul_div_cancel_left _ hp] using hm
  · intro a ha b hb hh
    exact Nat.eq_of_mul_eq_mul_left hp hh
  · intro n hn
    rcases mem_filter.mp hn with ⟨hn,hpn,hcut⟩
    exact ⟨n/p,hcut,Nat.mul_div_cancel' hpn⟩
  · intro m hm
    rw [Nat.mul_div_cancel_left _ hp]

lemma phase_log_mul_ramare {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    phase (Real.log (n*m:ℕ)) t=phase (Real.log n) t*phase (Real.log m) t := by
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hn.ne') (by exact_mod_cast hm.ne')]
  unfold phase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem binnedRamare_polynomial (P : Finset ℕ) (hP : ∀p∈P,0 < p)
    (M : ℕ → ℕ) (f : ℕ → ℂ) (U : ℕ) (hU : ∀p∈P,p*(2*M p)≤U) (t : ℝ) :
    polynomial (Ioc 0 U) (fun n => binnedRamareCoefficient P M f n/(n:ℂ))
      (fun n => Real.log n) t =
    ∑p∈P,(f p/(p:ℂ)*phase (Real.log p) t)*
      polynomial (Ioc (M p) (2*M p))
        (fun m => (f m/(primeCount P m+1:ℂ))/(m:ℂ)) (fun m => Real.log m) t := by
  classical
  unfold polynomial binnedRamareCoefficient
  simp_rw [sum_div,sum_mul,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have he : (∑n∈Ioc 0 U,
      (if p∣n ∧ n/p∈Finset.Ioc (M p) (2*M p) then f p*f (n/p)/(primeCount P (n/p)+1:ℂ) else 0)/(n:ℂ)*phase (Real.log n) t)=
      ∑m∈Ioc (M p) (2*M p),
        (f p*f m/(primeCount P m+1:ℂ))/(p*m:ℕ)*phase (Real.log (p*m:ℕ)) t := by
    have hh := bin_sum_by_multiples (hP p hp) (M p) U (hU p hp)
      (fun n m => (f p*f m/(primeCount P m+1:ℂ))/(n:ℂ)*phase (Real.log n) t)
    simpa only [ite_div,zero_div,ite_mul,zero_mul] using hh
  simp only [ite_div,zero_div,ite_mul,zero_mul] at he
  rw [he,mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := by have := (mem_Ioc.mp hm).1; omega
  rw [phase_log_mul_ramare (hP p hp) hm0,Nat.cast_mul]
  ring

theorem binnedRamare_polynomial_bins {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Q : ι → Finset ℕ) (P : Finset ℕ) (hP : ∀p∈P,0 < p)
    (hcov : P=S.biUnion Q) (hdisj : Set.PairwiseDisjoint (S:Set ι) Q)
    (M : ℕ → ℕ) (L : ι → ℕ) (hM : ∀i∈S,∀p∈Q i,M p=L i)
    (f : ℕ → ℂ) (U : ℕ) (hU : ∀p∈P,p*(2*M p)≤U) (t : ℝ) :
    polynomial (Ioc 0 U) (fun n => binnedRamareCoefficient P M f n/(n:ℂ))
      (fun n => Real.log n) t =
    ∑i∈S, (polynomial (Q i) (fun p => f p/(p:ℂ)) (fun p => Real.log p) t)*
      polynomial (Ioc (L i) (2*L i))
        (fun m => (f m/(primeCount P m+1:ℂ))/(m:ℂ)) (fun m => Real.log m) t := by
  classical
  rw [binnedRamare_polynomial P hP M f U hU t]
  conv_lhs => rw [hcov]
  rw [sum_biUnion hdisj]
  apply sum_congr rfl
  intro i hi
  conv_rhs => arg 1; unfold polynomial
  rw [sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [←hcov,hM i hi p hp]

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
