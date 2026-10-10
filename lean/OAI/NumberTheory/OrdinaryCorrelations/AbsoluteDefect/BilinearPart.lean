import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCount

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

namespace SourcePrimeFactor
open MeasureTheory

def bilinearPart (P : Finset ℕ) (f g : ℕ → ℂ) (v D : ℕ) : ℂ :=
  ∑ p ∈ P, f p * ∑ m ∈ (Finset.Ioc (v / p) ((v + D) / p)).filter (fun m => ¬p ∣ m),
    (f m * g (p * m)) / ((primeCount P m : ℂ) + 1)

lemma continuous_weightedFunction (f : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) :
    Continuous (fun z : ℝ => weightedFunction f P z n) := by
  unfold weightedFunction
  fun_prop

theorem cofactor_polynomial_integral (f g : ℕ → ℂ) (P S : Finset ℕ) (p : ℕ) :
    (∑ m ∈ S, (f m * g (p*m)) / ((primeCount P m : ℂ)+1)) =
    ∫ z in Set.Icc (0:ℝ) 1, ∑ m ∈ S, weightedFunction f P z m * g (p*m) := by
  have hi (n : ℕ) : IntegrableOn
      (fun z : ℝ => weightedFunction f P z n * g (p*n)) (Set.Icc 0 1) :=
    ((continuous_weightedFunction f P n).mul continuous_const).integrableOn_Icc
  rw [integral_finsetSum S (fun n hn => hi n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [MeasureTheory.integral_mul_const, cofactor_integral]
  ring

theorem bilinearPart_integral (f g : ℕ → ℂ) (P : Finset ℕ) (v D : ℕ) :
    bilinearPart P f g v D = ∫ z in Set.Icc (0:ℝ) 1,
      ∑ p ∈ P, f p * ∑ m ∈ (Finset.Ioc (v/p) ((v+D)/p)).filter (fun m => ¬p∣m),
        weightedFunction f P z m * g (p*m) := by
  unfold bilinearPart
  simp_rw [cofactor_polynomial_integral]
  have hc p : Continuous (fun z : ℝ => f p * ∑ m ∈
      (Finset.Ioc (v/p) ((v+D)/p)).filter (fun m => ¬p∣m),
        weightedFunction f P z m * g (p*m)) := by
    apply continuous_const.mul
    exact continuous_finsetSum _ (fun n hn => (continuous_weightedFunction f P n).mul continuous_const)
  rw [integral_finsetSum P (fun p hp => (hc p).integrableOn_Icc)]
  simp_rw [MeasureTheory.integral_const_mul]

theorem norm_bilinearPart_integral_le (f g : ℕ → ℂ) (P : Finset ℕ) (v D : ℕ) :
    ‖bilinearPart P f g v D‖ ≤ ∫ z in Set.Icc (0:ℝ) 1,
      ‖∑ p ∈ P, f p * ∑ m ∈ (Finset.Ioc (v/p) ((v+D)/p)).filter (fun m => ¬p∣m),
        weightedFunction f P z m * g (p*m)‖ := by
  rw [bilinearPart_integral]
  exact norm_integral_le_integral_norm _

end SourcePrimeFactor

end

end OAI
