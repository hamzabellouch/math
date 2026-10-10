import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseMulStar

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

theorem smoothed_prime_energy (P : Finset ℕ) (u : ℕ → ℂ)
    (hu : ∀n,‖u n‖≤1) (c : ℕ → ℂ) (hc : ∀p,‖c p‖≤1)
    (D a N K : ℕ) (α : ℝ) (hP : ∀p∈P,p≤K)
    {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    (∑n∈range N,‖∑p∈P,c p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n)‖^2) ≤
      (N:ℝ)*P.card+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ) := by
  let b := fun p n => c p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n)
  let E : ℝ := (2+4*(N:ℝ)*K/D)/κ
  have hE : 0≤E := by dsimp [E]; positivity
  have hb (p n : ℕ) : ‖b p n‖≤1 := by
    simp only [b,norm_mul,norm_phase,mul_one]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc p)).trans (smooth_bound u hu D _)
  have hd (p : ℕ) : ‖∑n∈range N,b p n*star (b p n)‖≤(N:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑n∈range N,(1:ℝ) := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul,norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hb p n)).trans (hb p n)
      _ = _ := by simp
  have ho (p : ℕ) (hp : p∈P) (q : ℕ) (hq : q∈P) (hpq : p≠q) :
      ‖∑n∈range N,b p n*star (b q n)‖≤E := by
    apply (smoothed_pair_bound u hu c hc D p q a N α hκ (hgap p hp q hq hpq)).trans
    have hpk : (p:ℝ)≤K := by exact_mod_cast hP p hp
    have hqk : (q:ℝ)≤K := by exact_mod_cast hP q hq
    apply div_le_div_of_nonneg_right _ hκ.le
    calc
      _ ≤ 2+(N:ℝ)*((2*(K:ℝ))*(2/(D:ℝ))) := by
        gcongr
        linarith
      _ = _ := by ring
  have hr (p : ℕ) (hp : p∈P) :
      ∑q∈P,‖∑n∈range N,b p n*star (b q n)‖≤(N:ℝ)+(P.card:ℝ)*E := by
    calc
      _ ≤ ∑q∈P,((if p=q then (N:ℝ) else 0)+E) := by
        apply sum_le_sum
        intro q hq
        by_cases he : p=q
        · subst q
          simpa using (hd p).trans (le_add_of_nonneg_right hE)
        · simpa [he] using ho p hp q hq he
      _ = _ := by simp [sum_add_distrib,hp]
  calc
    _ ≤ ∑p∈P,∑q∈P,‖∑n∈range N,b p n*star (b q n)‖ := energy_le_gram P b N
    _ ≤ ∑p∈P,((N:ℝ)+(P.card:ℝ)*E) := sum_le_sum hr
    _ = _ := by simp [E]; ring

end OrdinaryAdditiveBilinear

end

end OAI
