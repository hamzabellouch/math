import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDivisorReindex
import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeLogarithmicIdentity
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicReduction

namespace OAI

/-! # The prime bilinear reduction for squarefree-supported coefficients -/
namespace JointDickman
open Finset

noncomputable def primeSquareLogError (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, ∑ p ∈ n.primeFactors, if p^2 ∣ n then Real.log p else 0

noncomputable def primeLogBilinear (f : ArithmeticFunction ℝ) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p),
    ((f p*f m*Real.log p:ℝ):ℂ)*additivePhase ((p*m:ℕ)*θ)

lemma prime_log_bilinear_identity (f : ArithmeticFunction ℝ) (N : ℕ) (θ : ℝ) :
    (∑ n ∈ Ioc 0 N, ∑ p ∈ n.primeFactors,
      ((f p*f (n/p)*Real.log p:ℝ):ℂ)*additivePhase ((n:ℝ)*θ)) =
      primeLogBilinear f N θ := by
  unfold primeLogBilinear
  rw [←sum_prime_divisors_reindex]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro p hp
  rw [Nat.mul_div_cancel' (Nat.mem_primeFactors.mp hp).2.1]

lemma squarefree_logarithmic_bilinear_error (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    (hsupport : ∀ n, ¬Squarefree n → f n = 0) (N : ℕ) (θ : ℝ) :
    ‖(∑ n ∈ Ioc 0 N, ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ)) -
      primeLogBilinear f N θ‖ ≤ primeSquareLogError N := by
  rw [←prime_log_bilinear_identity,←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  have he : ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ) -
      (∑ p ∈ n.primeFactors, ((f p*f (n/p)*Real.log p:ℝ):ℂ)*additivePhase ((n:ℝ)*θ)) =
      ((f n*Real.log n - ∑ p ∈ n.primeFactors, f p*f (n/p)*Real.log p:ℝ):ℂ)*
        additivePhase ((n:ℝ)*θ) := by
    simp only [Complex.ofReal_sub,Complex.ofReal_sum,sub_mul,sum_mul]
  rw [he,norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact squarefree_supported_log_error f hf hb hsupport n

theorem squarefree_sum_prime_bilinear_reduction (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    (hsupport : ∀ n, ¬Squarefree n → f n = 0) (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    Real.log N * ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤
      (N:ℝ) + primeSquareLogError N + ‖primeLogBilinear f N θ‖ := by
  let g : ℕ → ℂ := fun n => (f n:ℂ)*additivePhase ((n:ℝ)*θ)
  have hg (n : ℕ) (hn : n ∈ Icc 1 N) : ‖g n‖ ≤ 1 := by
    simpa only [g,norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs] using hb n
  have hlog := unweighted_sum_le_logarithmic_sum g N hN hg
  have hi : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [←hi] at hlog
  have he : (∑ n ∈ Ioc 0 N, (Real.log n:ℂ)*g n) =
      ∑ n ∈ Ioc 0 N, ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ) := by
    apply sum_congr rfl
    intro n hn
    dsimp [g]
    push_cast
    ring
  rw [he] at hlog
  have hnorm := norm_le_norm_sub_add
    (∑ n ∈ Ioc 0 N, ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ))
    (primeLogBilinear f N θ)
  have herr := squarefree_logarithmic_bilinear_error f hf hb hsupport N θ
  change Real.log N * ‖∑ n ∈ Ioc 0 N, g n‖ ≤ _
  linarith

end JointDickman

end OAI
