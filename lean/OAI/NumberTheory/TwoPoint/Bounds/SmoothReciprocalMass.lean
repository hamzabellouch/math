import OAI.NumberTheory.TwoPoint.Bounds.SmoothDivisorDecomposition
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! Finite-prime smooth reciprocal sums. The exact Euler factors make
averaging the dilation cost against the padding law possible. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def smoothReciprocalProduct (P : Finset ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹

noncomputable def natNegativePower (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

lemma smoothReciprocalProduct_hasSum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    HasSum (fun a : Nat.factoredNumbers P => (a.val : ℝ) ^ (-s))
      (smoothReciprocalProduct P s) := by
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := natNegativePower s) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-s)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)) P
  have he : P.filter Nat.Prime = P := filter_eq_self.mpr hP
  simpa [natNegativePower, smoothReciprocalProduct, he] using h.2

lemma smoothReciprocalProduct_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    0 ≤ smoothReciprocalProduct P s := by
  apply (smoothReciprocalProduct_hasSum P hP s hs).nonneg
  intro a
  exact Real.rpow_nonneg (Nat.cast_nonneg a.val) _

lemma smooth_reciprocal_sum_le (P A : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s)
    (hA : ∀ a ∈ A, a ∈ Nat.factoredNumbers P) :
    (∑ a ∈ A, (a : ℝ) ^ (-s)) ≤ smoothReciprocalProduct P s := by
  let e : A → Nat.factoredNumbers P := fun a => ⟨a.val, hA a.val a.property⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : Nat.factoredNumbers P => x.val) hab
  have hb := sum_le_hasSum (univ.image e)
    (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg a.val) (-s))
    (smoothReciprocalProduct_hasSum P hP s hs)
  rw [sum_image (fun a _ b _ hab => he hab)] at hb
  rw [← sum_coe_sort A (fun a : ℕ => (a : ℝ) ^ (-s))]
  simpa only [e] using hb

/-- The geometric reciprocal cost of every smooth part of a bounded
integer is controlled independently of the outer bound. -/
lemma smooth_divisor_reciprocal_sum_le (q n : ℕ) (s : ℝ) (hs : 0 < s) :
    (∑ a ∈ n.divisors.filter (fun a => a.primeFactors ⊆ q.primeFactors),
      (a : ℝ) ^ (-s)) ≤ smoothReciprocalProduct q.primeFactors s := by
  apply smooth_reciprocal_sum_le _ _ (fun _ hp => Nat.prime_of_mem_primeFactors hp) s hs
  intro a ha
  obtain ⟨ha, has⟩ := mem_filter.mp ha
  exact Nat.mem_factoredNumbers_of_primeFactors_subset
    (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2)).ne' has

end TwoPointCorrelations

end OAI
