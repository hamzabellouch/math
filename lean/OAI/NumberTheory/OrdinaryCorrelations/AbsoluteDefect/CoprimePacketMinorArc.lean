import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CofactorNormLeOne

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

theorem coprime_packet_minor_arc (P : Finset ℕ) (hprime : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : ∀n,‖f n‖≤1) (hu : ∀n,‖u n‖≤1)
    (D N K : ℕ) (hN : 0<N) (α : ℝ) (hP : ∀p∈P,p≤K)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖coprimeRamarePacket P f u D N α‖ ≤
      Real.sqrt (((N:ℝ)*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card)*
        ((N:ℝ)*P.card+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ)))+
      (N:ℝ)*∑p∈P,(p:ℝ)⁻¹ := by
  have hm := Real.le_sqrt_of_sq_le
    (ramare_packet_minor_arc P hprime f u hf hu D N K hN α hP hL hκ hgap)
  have he := coprime_packet_error P hprime f u hf hu D N α
  have hi : coprimeRamarePacket P f u D N α=ramarePacket P f u D N α-
      (ramarePacket P f u D N α-coprimeRamarePacket P f u D N α) := by ring
  rw [hi]
  exact (norm_sub_le _ _).trans (add_le_add hm he)

theorem zero_frequency_no_gap (P : Finset ℕ) (hpq : ∃p∈P,∃q∈P,p≠q)
    {κ : ℝ} (hκ : 0<κ) :
    ¬(∀p∈P,∀q∈P,p≠q → κ≤‖1-phase ((0:ℝ)*((p:ℝ)-q))‖) := by
  intro h
  obtain ⟨p,hp,q,hq,hne⟩ := hpq
  have hh := h p hp q hq hne
  simp only [zero_mul,phase,Complex.ofReal_zero,mul_zero,Complex.exp_zero,sub_self,norm_zero] at hh
  exact (not_le_of_gt hκ) hh

end OrdinaryAdditiveBilinear

end

end OAI
