import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightedPartialSumBound
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCount
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothPart

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
open SourcePrimeFactor OrdinaryLogIntegral

lemma primeCount_rough_zero (P S : Finset ℕ) (hPS : P ⊆ S)
    (hP : ∀ p ∈ P, Nat.Prime p) {b : ℕ}
    (hb : ∀ p ∈ S, Nat.Prime p → ¬p∣b) : primeCount P b = 0 := by
  rw [primeCount, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hb p (hPS (mem_filter.mp hp).1) (hP p (mem_filter.mp hp).1) (mem_filter.mp hp).2

def cofactorTerm (f : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) (t : ℝ) : ℂ :=
  ((f n / (primeCount P n+1:ℂ)) / (n:ℂ)) * logPhase t n

lemma cofactorTerm_smooth_rough (f : ℕ → ℂ)
    (hm : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m*n)=f m*f n)
    (P S : Finset ℕ) (hPS : P ⊆ S) (hP : ∀ p ∈ P, Nat.Prime p)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (hsm : a ∈ Nat.factoredNumbers S)
    (hro : ∀ p ∈ S, Nat.Prime p → ¬p∣b) (t : ℝ) :
    cofactorTerm f P (a*b) t = cofactorTerm f P a t * ((f b/(b:ℂ))*logPhase t b) := by
  have hcop := smooth_coprime_rough hsm hro
  have hc := primeCount_rough_zero P S hPS hP hro
  simp only [cofactorTerm, primeCount_coprime_mul hP hcop, hc, Nat.add_zero,
    hm a b ha hb hcop, Nat.cast_mul,
    logPhase_mul t (x := (a:ℝ)) (y := (b:ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb)]
  ring

lemma rectangular_mul_injective (A B S : Finset ℕ)
    (hA : ∀ a ∈ A, 0<a ∧ a ∈ Nat.factoredNumbers S)
    (hB : ∀ b ∈ B, ∀ p ∈ S, Nat.Prime p → ¬p∣b) :
    Set.InjOn (fun ab : ℕ × ℕ => ab.1*ab.2) (A ×ˢ B : Finset (ℕ×ℕ)) := by
  intro ab hab cd hcd he
  change ab.1*ab.2 = cd.1*cd.2 at he
  have hab' := mem_product.mp hab
  have hcd' := mem_product.mp hcd
  have hac := factorization_unique (hA ab.1 hab'.1).2 (hA cd.1 hcd'.1).2
    (hB ab.2 hab'.2) (hB cd.2 hcd'.2) he
  have hbd : ab.2 = cd.2 := by
    rw [hac] at he
    exact Nat.eq_of_mul_eq_mul_left (hA cd.1 hcd'.1).1 he
  exact Prod.ext hac hbd

theorem rectangular_cofactor_factorization (f : ℕ → ℂ)
    (hm : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m*n)=f m*f n)
    (P S A B : Finset ℕ) (hPS : P ⊆ S) (hP : ∀ p ∈ P, Nat.Prime p)
    (hA : ∀ a ∈ A, 0<a ∧ a ∈ Nat.factoredNumbers S)
    (hB : ∀ b ∈ B, 0<b ∧ ∀ p ∈ S, Nat.Prime p → ¬p∣b) (t : ℝ) :
    (∑ n ∈ (A ×ˢ B).image (fun ab => ab.1*ab.2), cofactorTerm f P n t) =
      (∑ a ∈ A, cofactorTerm f P a t) * (∑ b ∈ B, (f b/(b:ℂ))*logPhase t b) := by
  rw [sum_image (fun ab hab cd hcd he => rectangular_mul_injective A B S hA
    (fun b hb => (hB b hb).2) hab hcd he), sum_product, sum_mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  exact cofactorTerm_smooth_rough f hm P S hPS hP (hA a ha).1 (hB b hb).1
    (hA a ha).2 (hB b hb).2 t

end OrdinarySmoothRough

end

end OAI
