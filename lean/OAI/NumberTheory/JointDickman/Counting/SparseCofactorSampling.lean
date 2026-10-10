import OAI.NumberTheory.JointDickman.Analysis.SparseIntegerMellin
import OAI.NumberTheory.TwoPointCorrelations.MRTCofactorMean

namespace OAI

/-! # Sparse sampling for the reciprocal-count cofactor used by Ramaré -/
namespace JointDickman
open Finset TwoPointCorrelations

/-- The sparse integer estimate applies to the literal cofactor, including
all bounded coefficient masks and the reciprocal prime-divisor count. -/
theorem sparse_ramare_cofactor_sampling (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    {T : ℝ} (hT : 0 ≤ T) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T) :
    (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤
      48000*(2*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T*a/N) := by
  let L := ⌊(N:ℝ)/a⌋₊+1
  let R := ⌊(2*N:ℝ)/a⌋₊
  have ha0 : 0 < a := by linarith
  have hU0 : 0 < (N:ℝ)/a := by linarith
  have hL : (N:ℝ)/a ≤ (L:ℝ) := by
    simpa only [L, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one ((N:ℝ)/a)).le
  have hR : (R:ℝ) ≤ 2*((N:ℝ)/a) := by
    change (⌊(2*N:ℝ)/a⌋₊:ℝ) ≤ _
    exact (Nat.floor_le (by positivity)).trans_eq (by ring)
  have hcoeff := mrt_reciprocal_count_oneBounded P F hF
  have hh := sparse_reciprocal_cofactor_sampling (U := (N:ℝ)/a) (by linarith)
    L R hL hR S hsep hT hdiam
    (fun n => (F n / ((finitePrimeDivisorCount P n + 1:ℕ):ℂ))/(n:ℂ)) (by
      intro n hn
      have hn0 : 0 < n := by
        have hl : 0 < L := by dsimp [L]; omega
        exact hl.trans_le (mem_Icc.mp hn).1
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (hcoeff n hn0) (Nat.cast_nonneg n))
  have he (t : ℝ) : mrtCofactorPolynomial P F N a t =
      mrtExponentialPolynomial (Icc L R)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1:ℕ):ℂ))/(n:ℂ))
        (fun n => -Real.log (n:ℝ)) t := by
    rw [mrt_cofactor_exponential_polynomial P F N ha]
    congr 1
    ext n
    simp only [mem_Ioc, mem_Icc, L, R]
    omega
  simp_rw [he]
  convert hh using 1
  congr 2
  field_simp

end JointDickman

end OAI
