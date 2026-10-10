import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseNatMul
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.UnitDual
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumMultiplesIoc

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

namespace OrdinaryCorrelations.SourcePrimeFactor
open OrdinaryAdditiveBilinear OrdinaryShortDual Finset

lemma dual_smooth_zero_left (F : ℕ → ℂ) (D U : ℕ) :
    smooth (actualDual F D U) D 0=0 := by
  unfold smooth
  apply mul_eq_zero_of_right
  apply sum_eq_zero
  intro j hj
  simpa only [zero_add] using actualDual_zero F D U j (Or.inl (Finset.mem_range.mp hj))

lemma dual_smooth_zero_right (F : ℕ → ℂ) (D U : ℕ) :
    smooth (actualDual F D U) D (U+D)=0 := by
  unfold smooth
  apply mul_eq_zero_of_right
  apply sum_eq_zero
  intro j hj
  exact actualDual_zero F D U ((U+D)+j) (Or.inr (by omega))

lemma sum_range_eq_Ioc (g : ℕ → ℂ) (M : ℕ) (h0 : g 0=0) (hM : g M=0) :
    (∑n∈range M,g n)=∑n∈Ioc 0 M,g n := by
  have ht := sum_range_sub g M
  rw [sum_sub_distrib,hM,h0,sub_self] at ht
  calc
    _ = ∑n∈range M,g (n+1) := (sub_eq_zero.mp ht).symm
    _ = _ := by
      apply sum_bij (fun n _ => n+1)
      · intro n hn
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Ioc]
        omega
      · intro n hn m hm he
        omega
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        exact ⟨m-1,Finset.mem_range.mpr (by omega),by omega⟩
      · intro n hn
        rfl

def dualTwist (f : ℕ → ℂ) (D U : ℕ) (α : ℝ) (n : ℕ) : ℂ :=
  smooth (actualDual (fun m => f m*phase (α*m)) D U) D n*phase (α*n)

lemma dualTwist_bound (f : ℕ → ℂ) (D U : ℕ) (α : ℝ) :
    OneBounded (dualTwist f D U α) := by
  intro n
  simp only [dualTwist,norm_mul,norm_phase,mul_one]
  exact smooth_bound _ (actualDual_bound _ D U) D n

theorem actual_short_prime_decomposition (P : Finset ℕ)
    (hP : ∀p∈P,Nat.Prime p) (f : ℕ → ℂ) (hf : Multiplicative f)
    (D U : ℕ) (α : ℝ) :
    (D:ℝ)⁻¹*(∑y∈range U,‖∑k∈range D,f (y+1+k)*phase (α*(y+1+k))‖)=
      ‖roughPart P f (dualTwist f D U α) 0 (U+D)+
        bilinearPart P f (dualTwist f D U α) 0 (U+D)+
        diagonalPart P f (dualTwist f D U α) 0 (U+D)‖ := by
  let F := fun m => f m*phase (α*m)
  have hd := actual_short_dual_witness F D U
  have hi : (∑m∈range (U+D),F m*((D:ℂ)⁻¹*∑j∈range D,actualDual F D U (m+j)))=
      roughPart P f (dualTwist f D U α) 0 (U+D)+
        bilinearPart P f (dualTwist f D U α) 0 (U+D)+
        diagonalPart P f (dualTwist f D U α) 0 (U+D) := by
    calc
      _ = ∑m∈range (U+D),f m*dualTwist f D U α m := by
        apply sum_congr rfl
        intro m hm
        dsimp [F,dualTwist,smooth]
        ring
      _ = ∑m∈Ioc 0 (U+D),f m*dualTwist f D U α m := by
        apply sum_range_eq_Ioc
        · simp only [dualTwist,dual_smooth_zero_left,zero_mul,mul_zero]
        · simp only [dualTwist,dual_smooth_zero_right,zero_mul,mul_zero]
      _ = _ := by simpa only [zero_add] using
        short_sum_decomposition P hP f (dualTwist f D U α) hf 0 (U+D)
  rw [hi] at hd
  simpa only [F,shortSum,Nat.cast_add,Nat.cast_one] using hd

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
