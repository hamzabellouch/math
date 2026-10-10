import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCount
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CharacterModulation
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Bump

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

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare OrdinaryGaussianWindow
open Finset Filter MeasureTheory

lemma dyadic_coefficient_sum {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {X : ℕ} (hX : 0<X) :
    (∑n∈Ioc X (2*X),‖characterModulation f χ n/(n:ℂ)‖)≤1 := by
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  calc
    _ ≤ ∑n∈Ioc X (2*X),(X:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hnX : (X:ℝ)≤n := by exact_mod_cast (mem_Ioc.mp hn).1.le
      have hnpos : (0:ℝ)<n := hXr.trans_le hnX
      rw [norm_div,Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (characterModulation_bound hf χ n) hnpos.le).trans
        (by simpa only [one_div] using inv_le_inv₀ hnpos hXr |>.2 hnX)
    _ = 1 := by
      simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul]
      have he : 2*X-X=X := by omega
      rw [he,mul_inv_cancel₀ hXr.ne']

lemma dyadic_log_centres {X : ℕ} (hX : 0<X) : ∀n∈Finset.Ioc X (2*X),
    Real.log (X:ℝ)≤Real.log (n:ℝ) ∧ Real.log (n:ℝ)≤Real.log (X:ℝ)+1 := by
  intro n hn
  obtain ⟨hnlo,hnhi⟩ := Finset.mem_Ioc.mp hn
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  have hnr : (0:ℝ)<n := by exact_mod_cast (hX.trans hnlo)
  constructor
  · exact Real.log_le_log hXr (by exact_mod_cast hnlo.le)
  · have hh := Real.log_le_log hnr (show (n:ℝ)≤2*(X:ℝ) by exact_mod_cast hnhi)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hXr.ne'] at hh
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith

end OrdinaryChainScales

end

end OAI
