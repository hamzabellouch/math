import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Poly
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseAdd
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ArithmeticGeneratingUpper

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

namespace OrdinaryAdditiveBilinear
open Finset

lemma sum_range_succ_eq_Icc (N : ℕ) (g : ℕ → ℝ) :
    (∑n∈range N,g (1+n))=∑m∈Icc 1 N,g m := by
  apply sum_bij (fun n _ => 1+n)
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro n hn m hm he
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    refine ⟨m-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro n hn
    rfl

def ramarePacket (P : Finset ℕ) (f u : ℕ → ℂ) (D N : ℕ) (α : ℝ) : ℂ :=
  ∑p∈P,f p*∑n∈range N,
    (f (1+n)/((OrdinaryCorrelations.SourcePrimeFactor.primeCount P (1+n):ℂ)+1))*
      smooth u D (p*(1+n))*phase (α*(p:ℝ)*(1+n))

theorem ramare_packet_minor_arc (P : Finset ℕ) (hprime : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : ∀n,‖f n‖≤1) (hu : ∀n,‖u n‖≤1)
    (D N K : ℕ) (hN : 0<N) (α : ℝ) (hP : ∀p∈P,p≤K)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖ramarePacket P f u D N α‖^2 ≤
      ((N:ℝ)*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card)*
        ((N:ℝ)*P.card+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ)) := by
  let w := fun n => f n/((OrdinaryCorrelations.SourcePrimeFactor.primeCount P n:ℂ)+1)
  have ha := OrdinaryCofactorWeight.arithmetic_cofactor_second_moment P hprime hN hL f hf
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hw : (∑n∈range N,‖w (1+n)‖^2)≤
      (N:ℝ)*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card := by
    rw [sum_range_succ_eq_Icc N (fun n => ‖w n‖^2)]
    have hh := (mul_le_mul_of_nonneg_left ha hNr.le)
    simpa only [w,OrdinaryCorrelations.SourcePrimeFactor.primeCount,←mul_assoc,mul_inv_cancel₀ hNr.ne',
      one_mul,mul_add,mul_div_cancel₀ _ hNr.ne'] using hh
  have hb := smoothed_weighted_packet P u w f hu hf D 1 N K α hP hκ hgap
  have hh : ‖ramarePacket P f u D N α‖^2 ≤ (∑n∈range N,‖w (1+n)‖^2)*
      ((N:ℝ)*P.card+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ)) := by
    simpa only [ramarePacket,w,Nat.cast_one] using hb
  exact hh.trans (mul_le_mul_of_nonneg_right hw (by positivity))

end OrdinaryAdditiveBilinear

end

end OAI
