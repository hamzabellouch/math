import OAI.Analysis.Pureness.Comparison.TraceBounds
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

namespace OAI
open scoped ComplexOrder
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma alternating_pow (x y : A) (n : ℕ) : (x * y)^n * x = x * (y * x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (x * y)^(n + 1) * x = ((x * y)^n * x) * (y * x) := by simp only [pow_succ, mul_assoc]
      _ = (x * (y * x)^n) * (y * x) := by rw [ih]
      _ = x * (y * x)^(n + 1) := by rw [pow_succ, mul_assoc]

omit [StarOrderedRing A] in
lemma TracialState.linking_power_trace (τ : TracialState A) (z : A) (n : ℕ) :
    τ.toPositiveLinearMap ((star z * z)^n) = τ.toPositiveLinearMap ((z * star z)^n) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [pow_succ, ← mul_assoc, alternating_pow]
    rw [τ.tracial]
    congr 1
    rw [← mul_assoc, ← pow_succ']

omit [StarOrderedRing A] in
lemma TracialState.linking_polynomial_trace (τ : TracialState A) (z : A) (p : Polynomial ℝ) :
    τ.toPositiveLinearMap (Polynomial.aeval (star z * z) p) =
      τ.toPositiveLinearMap (Polynomial.aeval (z * star z) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    change (τ.toPositiveLinearMap.toLinearMap.restrictScalars ℝ) (r • (star z * z)^n) =
      (τ.toPositiveLinearMap.toLinearMap.restrictScalars ℝ) (r • (z * star z)^n)
    rw [map_smul, map_smul]
    exact congrArg (r • ·) (τ.linking_power_trace z n)

theorem TracialState.linking_cfc_trace (τ : TracialState A) (z : A)
    (f : ℝ → ℝ) (hf : Continuous f) :
    τ.toPositiveLinearMap (cfc f (star z * z)) =
      τ.toPositiveLinearMap (cfc f (z * star z)) := by
  nontriviality A
  let a := star z * z
  let b := z * star z
  have ha : IsSelfAdjoint a := (star_mul_self_nonneg z).isSelfAdjoint
  have hb : IsSelfAdjoint b := (mul_star_self_nonneg z).isSelfAdjoint
  let R := max ‖a‖ ‖b‖
  have hspec {c : A} (hc : ‖c‖ ≤ R) : spectrum ℝ c ⊆ Set.Icc (-R) R := by
    intro t ht
    have h := (spectrum.norm_le_norm_of_mem ht).trans hc
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using h)
  apply eq_of_norm_sub_le_zero
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R f hf.continuousOn
    (ε / 2) (half_pos hε)
  have hbound {c : A} (hc : IsSelfAdjoint c) (hn : ‖c‖ ≤ R) :
      ‖cfc f c - Polynomial.aeval c p‖ ≤ ε / 2 := by
    rw [← cfc_polynomial p c, ← cfc_sub f (fun x => p.eval x) c]
    apply norm_cfc_le (half_pos hε).le
    intro t ht
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (hp t (hspec hn ht)).le
  have htrace := τ.linking_polynomial_trace z p
  have h1 : ‖τ.toPositiveLinearMap (cfc f a) -
      τ.toPositiveLinearMap (Polynomial.aeval a p)‖ ≤ ε / 2 := by
    rw [← map_sub]
    exact (τ.norm_apply_le_norm _).trans (hbound ha (le_max_left _ _))
  have h2 : ‖τ.toPositiveLinearMap (Polynomial.aeval b p) -
      τ.toPositiveLinearMap (cfc f b)‖ ≤ ε / 2 := by
    rw [norm_sub_rev, ← map_sub]
    exact (τ.norm_apply_le_norm _).trans (hbound hb (le_max_right _ _))
  have heq : τ.toPositiveLinearMap (cfc f a) - τ.toPositiveLinearMap (cfc f b) =
      (τ.toPositiveLinearMap (cfc f a) - τ.toPositiveLinearMap (Polynomial.aeval a p)) +
      (τ.toPositiveLinearMap (Polynomial.aeval b p) - τ.toPositiveLinearMap (cfc f b)) := by
    rw [show τ.toPositiveLinearMap (Polynomial.aeval a p) =
      τ.toPositiveLinearMap (Polynomial.aeval b p) from htrace]
    abel
  change ‖τ.toPositiveLinearMap (cfc f a) - τ.toPositiveLinearMap (cfc f b)‖ ≤ 0 + ε
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)
end CuntzComparison

end OAI
