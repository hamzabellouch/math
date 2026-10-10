import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseAdd
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumRangeCut

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

theorem truncated_weighted_packet (P : Finset ℕ) (u w c : ℕ → ℂ)
    (hu : ∀n,‖u n‖≤1) (hc : ∀p,‖c p‖≤1)
    (T : ℕ → ℕ) (D a N K : ℕ) (hT : ∀p∈P,T p≤N) (α : ℝ)
    (hP : ∀p∈P,p≤K) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖∑p∈P,c p*∑n∈range (T p),w (a+n)*smooth u D (p*(a+n))*
      phase (α*(p:ℝ)*(a+n))‖^2 ≤
      (∑n∈range N,‖w (a+n)‖^2)*
        ((N:ℝ)*P.card+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ)) := by
  let c' := fun p => c p*phase (α*(p:ℝ)*a)
  have hc' (p : ℕ) : ‖c' p‖≤1 := by simpa [c',norm_mul,norm_phase] using hc p
  let b := fun n => ∑p∈P,if n<T p then
    c' p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n) else 0
  have hi : (∑p∈P,c p*∑n∈range (T p),w (a+n)*smooth u D (p*(a+n))*
      phase (α*(p:ℝ)*(a+n))) = ∑n∈range N,w (a+n)*b n := by
    calc
      _ = ∑p∈P,∑n∈range N,if n<T p then
          c p*(w (a+n)*smooth u D (p*(a+n))*phase (α*(p:ℝ)*(a+n))) else 0 := by
        apply sum_congr rfl
        intro p hp
        rw [sum_range_cut _ N (T p) (hT p hp),mul_sum]
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro n hn
        simp only [b,mul_sum]
        apply sum_congr rfl
        intro p hp
        split_ifs
        · have he : α*(p:ℝ)*(a+n)=α*(p:ℝ)*a+α*(p:ℝ)*n := by ring
          rw [he,phase_add]
          dsimp [c']
          ring
        · simp
  rw [hi]
  apply (weighted_packet_sq (range N) (fun n => w (a+n)) b).trans
  exact mul_le_mul_of_nonneg_left
    (truncated_smoothed_prime_energy P u hu c' hc' T D a N K hT α hP hκ hgap)
    (sum_nonneg (fun n hn => sq_nonneg _))

end OrdinaryAdditiveBilinear

end

end OAI
