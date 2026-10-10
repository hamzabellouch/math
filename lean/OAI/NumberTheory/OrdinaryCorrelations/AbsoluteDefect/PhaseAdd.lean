import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothedPrimeEnergy

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

lemma phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  unfold phase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

lemma weighted_packet_sq (S : Finset ℕ) (w b : ℕ → ℂ) :
    ‖∑n∈S,w n*b n‖^2 ≤ (∑n∈S,‖w n‖^2)*(∑n∈S,‖b n‖^2) := by
  calc
    _ ≤ (∑n∈S,‖w n‖*‖b n‖)^2 := by
      gcongr
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ _ := sum_mul_sq_le_sq_mul_sq S (fun n => ‖w n‖) (fun n => ‖b n‖)

theorem smoothed_weighted_packet (P : Finset ℕ) (u w c : ℕ → ℂ)
    (hu : ∀n,‖u n‖≤1) (hc : ∀p,‖c p‖≤1)
    (D a N K : ℕ) (α : ℝ) (hP : ∀p∈P,p≤K)
    {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖∑p∈P,c p*∑n∈range N,w (a+n)*smooth u D (p*(a+n))*
      phase (α*(p:ℝ)*(a+n))‖^2 ≤
      (∑n∈range N,‖w (a+n)‖^2)*
        ((N:ℝ)*P.card+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ)) := by
  let c' := fun p => c p*phase (α*(p:ℝ)*a)
  have hc' (p : ℕ) : ‖c' p‖≤1 := by simpa [c',norm_mul,norm_phase] using hc p
  let b := fun n => ∑p∈P,c' p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n)
  have hi : (∑p∈P,c p*∑n∈range N,w (a+n)*smooth u D (p*(a+n))*
      phase (α*(p:ℝ)*(a+n))) = ∑n∈range N,w (a+n)*b n := by
    simp only [mul_sum,b]
    rw [sum_comm]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro p hp
    have he : α*(p:ℝ)*(a+n)=α*(p:ℝ)*a+α*(p:ℝ)*n := by ring
    rw [he,phase_add]
    dsimp [c']
    ring
  rw [hi]
  apply (weighted_packet_sq (range N) (fun n => w (a+n)) b).trans
  exact mul_le_mul_of_nonneg_left
    (smoothed_prime_energy P u hu c' hc' D a N K α hP hκ hgap)
    (sum_nonneg (fun n hn => sq_nonneg _))

end OrdinaryAdditiveBilinear

end

end OAI
