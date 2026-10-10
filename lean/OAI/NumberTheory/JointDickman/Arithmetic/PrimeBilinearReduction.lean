import OAI.NumberTheory.JointDickman.Probability.GeometricSquareKernel
import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairCorrelations
import OAI.NumberTheory.JointDickman.Amplification.ChebyshevDischarge

namespace OAI

/-! # Reducing a prime bilinear sum to its rational-frequency kernel -/
namespace JointDickman
open Finset

/-- The finite smoothed estimate before the rational-frequency summation.
The width X bounds only the prime differences; Q bounds the prime locations. -/
theorem prime_bilinear_kernel_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (Q X Y : ℕ) (P : Finset ℕ) (b : ℕ → ℂ) (c : ℤ → ℂ) (θ : ℝ) (a : ℤ),
    2 ≤ Q → (∀ p ∈ P, p.Prime ∧ p ≤ Q) →
    (∀ p ∈ P, ∀ r ∈ P, r-p ≤ X) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log Q) →
    (∀ n ∈ Ico a (a+Y), ‖c n‖ ≤ 1) →
    ‖∑ n ∈ Ico a (a+Y), c n * ∑ p ∈ P, b p * additivePhase (θ*p*n)‖^2 ≤
      C*((Q:ℝ)*Real.log Q*(Y:ℝ)^2 + (Q:ℝ)*
        ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*geometricSquareKernel (2*Y) (θ*h)) := by
  obtain ⟨C₁,hC₁,hpair⟩ := prime_even_kernel_bound
  obtain ⟨C₂,hC₂,hcount⟩ := chebyshevPrimeCountingInput
  refine ⟨4*C₂+2*C₁,by positivity,?_⟩
  intro Q X Y P b c θ a hQ hP hspan hb hc
  have hQ' : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hcountP : (P.card:ℝ) ≤ C₂*(Q:ℝ)/Real.log Q := by
    have hsub : P ⊆ Nat.primesLE Q := fun p hp => Nat.mem_primesLE.mpr ⟨(hP p hp).2,(hP p hp).1⟩
    have hcard : (P.card:ℝ) ≤ Nat.primeCounting Q := by
      exact_mod_cast (card_le_card hsub).trans_eq (Nat.primesLE_card_eq_primeCounting Q)
    exact hcard.trans (by simpa using hcount Q hQ')
  let K := fun h : ℤ => geometricSquareKernel (2*Y) (θ*h)
  have hK : ∀ h, 0 ≤ K h := fun h => geometricSquareKernel_nonneg _ _
  have heven : ∀ h, K (-h) = K h := by
    intro h
    simp only [K,Int.cast_neg,mul_neg,geometricSquareKernel_neg]
  have hpairs := hpair Q X P hQ hP hspan K hK heven
  have hgeom (p r : ℕ) :
      ‖∑ u ∈ Ico (0:ℤ) (2*Y), additivePhase (θ*((p:ℝ)-r)*u)‖^2 = K ((r:ℤ)-p) := by
    have hg := geometricSquareKernel_int_Ico (2*Y) (θ*((p:ℝ)-r))
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hg
    rw [hg]
    change geometricSquareKernel (2*Y) (θ*((p:ℝ)-r)) =
      geometricSquareKernel (2*Y) (θ*(((r:ℤ)-p:ℤ):ℝ))
    rw [Int.cast_sub,Int.cast_natCast,Int.cast_natCast,
      show θ*((p:ℝ)-r) = -(θ*((r:ℝ)-p)) by ring,geometricSquareKernel_neg]
  have hcoeff : (∑ p ∈ P, ∑ r ∈ P, ‖b p‖*‖b r‖*
      ‖∑ u ∈ Ico (0:ℤ) (2*Y), additivePhase (θ*((p:ℝ)-r)*u)‖^2) ≤
      (Real.log Q)^2 * ∑ p ∈ P, ∑ r ∈ P, K ((r:ℤ)-p) := by
    simp only [mul_sum]
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro r hr
    rw [hgeom]
    apply mul_le_mul_of_nonneg_right _ (hK _)
    simpa only [pow_two] using mul_le_mul (hb p hp) (hb r hr) (norm_nonneg _) hlog.le
  have hmain := (smoothed_bilinear_bound P b c θ a Y hc).trans
    (hcoeff.trans (mul_le_mul_of_nonneg_left hpairs (sq_nonneg (Real.log Q))))
  have hdiag : (Real.log Q)^2*(P.card:ℝ)*(2*(Y:ℝ))^2 ≤
      4*C₂*((Q:ℝ)*Real.log Q*(Y:ℝ)^2) := by
    have hh := mul_le_mul_of_nonneg_left hcountP
      (show 0 ≤ (Real.log Q)^2*(2*(Y:ℝ))^2 by positivity)
    convert hh using 1 <;> field_simp
    ring
  have heq : (Real.log Q)^2*((P.card:ℝ)*K 0 +
      2*C₁*(Q:ℝ)/(Real.log Q)^2 * ∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h) =
      (Real.log Q)^2*(P.card:ℝ)*(2*(Y:ℝ))^2 +
      2*C₁*((Q:ℝ)*∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h) := by
    simp only [K,Int.cast_zero,mul_zero,geometricSquareKernel_zero,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  rw [heq] at hmain
  have hA : 0 ≤ (Q:ℝ)*Real.log Q*(Y:ℝ)^2 := by positivity
  have hB : 0 ≤ (Q:ℝ)*∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact sum_nonneg (fun h _ => mul_nonneg (by positivity) (hK h))
  change _ ≤ (4*C₂+2*C₁)*((Q:ℝ)*Real.log Q*(Y:ℝ)^2 +
    (Q:ℝ)*∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*K h)
  nlinarith [mul_nonneg hC₂ hB,mul_nonneg hC₁.le hA]

end JointDickman

end OAI
