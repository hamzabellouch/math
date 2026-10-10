import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI

/-!
# Local positive moments without independence

The probabilistic summation in `lem:local-moment` of paper 031-01.
The distribution may live on an arbitrary countable set, and all component
correlations are allowed. A geometric bound on the maximum valuation
implies a positive moment bound.
-/

open scoped ENNReal

namespace DukePrimeDegree

/-- Upper tail of a natural-number-valued random variable, written for a
 nonnegative discrete mass function. -/
noncomputable def valuationTail {Ω : Type*} (p : Ω → ℝ≥0∞) (j : Ω → ℕ)
    (a : ℕ) : ℝ≥0∞ := ∑' ω, if a ≤ j ω then p ω else 0

/-- The tail of a maximum is bounded by the sum of the component tails.
No independence assumption is present. The positive threshold also
covers the possibility of an empty index type. -/
theorem valuationTail_sup_le_sum {Ω I : Type*} [Fintype I]
    (p : Ω → ℝ≥0∞) (j : I → Ω → ℕ) (a : ℕ) (ha : 0 < a) :
    valuationTail p (fun ω => Finset.univ.sup (fun i => j i ω)) a ≤
      ∑ i, valuationTail p (j i) a := by
  classical
  calc
    _ ≤ ∑' ω, ∑ i, if a ≤ j i ω then p ω else 0 := by
      apply ENNReal.tsum_le_tsum
      intro ω
      split_ifs with h
      · obtain ⟨i, hi, hji⟩ := (Finset.le_sup_iff ha).mp h
        calc
          p ω = (if a ≤ j i ω then p ω else 0) := (ite_eq_left hji).symm
          _ ≤ ∑ i, if a ≤ j i ω then p ω else 0 :=
            Finset.single_le_sum (f := fun i => if a ≤ j i ω then p ω else 0)
              (fun _ _ => zero_le) hi
      · exact zero_le
    _ = ∑ i, valuationTail p (j i) a := by
      simpa only [valuationTail, tsum_fintype] using
        (ENNReal.tsum_comm (f := fun ω i => if a ≤ j i ω then p ω else 0))

/-- A tail bound controls the local norm moment. In the application,
`r = ℓ^(n*s)`, `t = ℓ⁻¹`, and `C = n`. -/
theorem moment_le_of_valuation_tail {Ω : Type*}
    (p : Ω → ℝ≥0∞) (j : Ω → ℕ) (r t C : ℝ≥0∞)
    (htotal : ∑' ω, p ω = 1)
    (htail : ∀ a : ℕ, valuationTail p j (a + 1) ≤ C * t ^ (a + 1)) :
    (∑' ω, p ω * r ^ j ω) ≤
      1 + C * ∑' a : ℕ, (r * t) ^ (a + 1) := by
  have hpoint (ω : Ω) : r ^ j ω ≤ ∑' a : ℕ, if a ≤ j ω then r ^ a else 0 := by
    simpa using
      (ENNReal.le_tsum (f := fun a : ℕ => if a ≤ j ω then r ^ a else 0) (j ω))
  have hswap : (∑' ω, p ω * ∑' a : ℕ, if a ≤ j ω then r ^ a else 0) =
      ∑' a : ℕ, r ^ a * valuationTail p j a := by
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    congr 1
    funext a
    simp only [valuationTail, ← ENNReal.tsum_mul_left]
    congr 1
    funext ω
    split <;> simp_all [mul_comm]
  calc
    (∑' ω, p ω * r ^ j ω)
      ≤ ∑' ω, p ω * ∑' a : ℕ, if a ≤ j ω then r ^ a else 0 :=
        ENNReal.tsum_le_tsum (fun ω => mul_le_mul_right (hpoint ω) (p ω))
    _ = ∑' a : ℕ, r ^ a * valuationTail p j a := hswap
    _ = 1 + ∑' a : ℕ, r ^ (a + 1) * valuationTail p j (a + 1) := by
      rw [tsum_eq_zero_add' ENNReal.summable]
      simp only [pow_zero, one_mul, valuationTail, Nat.zero_le, ite_true, htotal]
    _ ≤ 1 + ∑' a : ℕ, r ^ (a + 1) * (C * t ^ (a + 1)) := by
      exact add_le_add_right (ENNReal.tsum_le_tsum fun a =>
        mul_le_mul_right (htail a) (r ^ (a + 1))) 1
    _ = 1 + C * ∑' a : ℕ, (r * t) ^ (a + 1) := by
      simp only [mul_pow, ← ENNReal.tsum_mul_left]
      congr 1
      congr 1
      funext a
      ac_rfl

/-- Closed-form version of the same estimate. For a rational prime ℓ and
`s = 1/(2*n)`, the ratio `r*t` becomes `ℓ^(-1/2) < 1`. -/
theorem moment_le_geometric_bound {Ω : Type*}
    (p : Ω → ℝ≥0∞) (j : Ω → ℕ) (r t C : ℝ≥0∞)
    (htotal : ∑' ω, p ω = 1)
    (htail : ∀ a : ℕ, valuationTail p j (a + 1) ≤ C * t ^ (a + 1)) :
    (∑' ω, p ω * r ^ j ω) ≤ 1 + C * ((r * t) * (1 - r * t)⁻¹) := by
  simpa only [ENNReal.tsum_geometric_add_one] using
    moment_le_of_valuation_tail p j r t C htotal htail

/-- Component tail estimates imply the local norm-moment estimate,
with precisely the number of components as the union-bound factor. -/
theorem moment_sup_le_geometric_bound {Ω I : Type*} [Fintype I]
    (p : Ω → ℝ≥0∞) (j : I → Ω → ℕ) (r t : ℝ≥0∞)
    (htotal : ∑' ω, p ω = 1)
    (htail : ∀ i a, valuationTail p (j i) (a + 1) ≤ t ^ (a + 1)) :
    (∑' ω, p ω * r ^ Finset.univ.sup (fun i => j i ω)) ≤
      1 + (Fintype.card I : ℝ≥0∞) * ((r * t) * (1 - r * t)⁻¹) := by
  apply moment_le_geometric_bound p _ r t (Fintype.card I) htotal
  intro a
  calc
    _ ≤ ∑ i, valuationTail p (j i) (a + 1) :=
      valuationTail_sup_le_sum p j (a + 1) (Nat.succ_pos a)
    _ ≤ ∑ _i : I, t ^ (a + 1) := Finset.sum_le_sum fun i _ => htail i a
    _ = (Fintype.card I : ℝ≥0∞) * t ^ (a + 1) := by simp [nsmul_eq_mul]

end DukePrimeDegree

end OAI
