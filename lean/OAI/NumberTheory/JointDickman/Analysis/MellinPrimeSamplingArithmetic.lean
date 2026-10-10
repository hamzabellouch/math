import OAI.NumberTheory.JointDickman.Analysis.MellinSieveUniform
import OAI.NumberTheory.JointDickman.Analysis.MellinPrimeSampling

namespace OAI

/-! # Prime sampling with the divisor errors discharged -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

/-- Sparse-prime sampling with explicit divisor-sum error bounds. -/
theorem mellin_prime_sampling_arithmetic (B : ℝ) (hB : 1 ≤ B) :
    ∃ C A δ V : ℝ, 0 < C ∧ 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (q Z : ℕ) (P Q : Finset ℕ) (N : ℝ) (S : Finset ℝ),
      16 ≤ q → 2 ≤ Z → Z ≤ q → V ≤ (q:ℝ)^9 →
      (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z) →
      (∀ p ∈ Q, p.Prime ∧ Z < p ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ (q:ℝ)^B) →
      ∀ a : ℕ → ℂ,
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q a (fun n => -Real.log (n:ℝ)) t‖^2) ≤
        8*(32*C*N*(∏ p ∈ P, (1-1/(p:ℝ))) + (Z+1:ℕ)*
          (6*(q:ℝ)^9 + (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ))*S.card)*
            ∑ p ∈ Q, ‖a p‖^2 := by
  obtain ⟨C,hC,hsample⟩ := mellin_prime_sampling
  obtain ⟨A,δ,V,hA,hδ,hδ1,hkernel⟩ := mellinSieve_integer_scale_uniform B hB
  refine ⟨C,A,δ,V,hC,hA,hδ,hδ1,?_⟩
  intro q Z P Q N S hq hZ hZq hV hNl hNu hP hQ hsep hdiam a
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN : 0 < N := (pow_pos hq0 10).trans_le hNl
  have hQK : Q ⊆ Icc 1 (q^12) := by
    intro p hp
    apply mem_Icc.mpr
    refine ⟨(hQ p hp).1.one_le, ?_⟩
    have hq2 : (2:ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    have hcut : 2*N ≤ (q:ℝ)^12 := by
      apply (mul_le_mul_of_nonneg_left hNu (by norm_num : (0:ℝ) ≤ 2)).trans
      calc
        2*(q:ℝ)^11 ≤ (q:ℝ)*(q:ℝ)^11 := mul_le_mul_of_nonneg_right hq2 (pow_nonneg hq0.le 11)
        _ = _ := by ring
    exact_mod_cast (hQ p hp).2.2.2.trans hcut
  apply hsample (q^12) Z P Q N S _ hZ hN (by positivity) hP hQK
    (fun p hp => ⟨(hQ p hp).1, (hQ p hp).2.1⟩)
    (fun p hp => (hQ p hp).2.2) hsep _ a
  intro D hD x hx y hy
  have hDP : D ⊆ P := mem_powerset.mp (mem_filter.mp hD).1
  have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp => (hP p (hDP hp)).1.pos)
  have hdq : (∏ p ∈ D, p) ≤ q := (mem_filter.mp hD).2.trans hZq
  exact hkernel q (∏ p ∈ D, p) hq hd hdq hV N (x-y) hNl hNu (hdiam x hx y hy)

end JointDickman

end OAI
