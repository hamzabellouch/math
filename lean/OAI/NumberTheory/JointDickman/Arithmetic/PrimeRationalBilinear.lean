import OAI.NumberTheory.JointDickman.Arithmetic.PrimeBilinearReduction
import OAI.NumberTheory.JointDickman.Probability.WeightedRationalKernel

namespace OAI

/-! # A rational-frequency bound for a prime--integer rectangle -/
namespace JointDickman
open Finset

theorem prime_rational_bilinear_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (Q X Y q a : ℕ) (P : Finset ℕ) (b : ℕ → ℂ) (c : ℤ → ℂ) (v : ℤ),
    2 ≤ Q → 1 ≤ X → 0 < q → a.Coprime q →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) → (∀ p ∈ P, ∀ r ∈ P, r-p ≤ X) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log Q) →
    (∀ n ∈ Ico v (v+Y), ‖c n‖ ≤ 1) →
    ‖∑ n ∈ Ico v (v+Y), c n * ∑ p ∈ P, b p * additivePhase ((a:ℝ)/q*p*n)‖^2 ≤
      C*((Q:ℝ)*Real.log Q*(Y:ℝ)^2 +
        Q*(Y:ℝ)^2*X*(1+Real.log q)/q + Q*Y*X + Q*Y*q*(1+Real.log X)) := by
  obtain ⟨C,hC,hbase⟩ := prime_bilinear_kernel_bound
  refine ⟨8*Real.exp 2*C,by positivity,?_⟩
  intro Q X Y q a P b c v hQ hX hq ha hP hspan hb hc
  let A := (Q:ℝ)*Real.log Q*(Y:ℝ)^2
  let B := (Y:ℝ)^2*X*(1+Real.log q)/q
  let D := (Y:ℝ)*X
  let E := (Y:ℝ)*q*(1+Real.log X)
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hXlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hi : Ioc 0 X = Icc 1 X := by
    ext h
    simp only [mem_Ioc,mem_Icc]
    omega
  have hk := totient_weighted_rational_kernel_bound q hq a ha (2*Y) X
  rw [hi] at hk
  have hk' : (∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*
      geometricSquareKernel (2*Y) ((a:ℝ)/q*h)) ≤
      2*Real.exp 2*(4*B+2*D+2*E) := by
    convert hk using 1
    dsimp [B,D,E]
    push_cast
    ring
  have hk'' : (∑ h ∈ Icc 1 X, ((h:ℝ)/h.totient)*
      geometricSquareKernel (2*Y) ((a:ℝ)/q*h)) ≤ 8*Real.exp 2*(B+D+E) := by
    apply hk'.trans
    nlinarith [mul_nonneg (Real.exp_pos 2).le hD,mul_nonneg (Real.exp_pos 2).le hE]
  have hp := hbase Q X Y P b c ((a:ℝ)/q) v hQ hP hspan hb hc
  have hp' := hp.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hk'' (Nat.cast_nonneg Q))) hC.le)
  have hexp : 1 ≤ 8*Real.exp 2 := by
    have h := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have heq : (Q:ℝ)*Real.log Q*(Y:ℝ)^2 +
      Q*(Y:ℝ)^2*X*(1+Real.log q)/q + Q*Y*X + Q*Y*q*(1+Real.log X) =
      A+(Q:ℝ)*(B+D+E) := by dsimp [A,B,D,E]; ring
  rw [heq]
  change _ ≤ C*(A+(Q:ℝ)*(8*Real.exp 2*(B+D+E))) at hp'
  apply hp'.trans
  have haexp := mul_le_mul_of_nonneg_right hexp hA
  nlinarith

end JointDickman

end OAI
