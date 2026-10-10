import OAI.Analysis.FactorGeneration.ProjectionLimits
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! Finite dyadic roots of unity, with a refinement estimate. These are the
scalar coefficients for the norm-convergent Haar-unitary construction. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial
open scoped BigOperators

def dyadicRank : (n : ℕ) → DyadicIndex n → ℕ
  | 0, _ => 0
  | n + 1, i => 2 * dyadicRank n i.1 + if i.2 then 1 else 0

theorem sum_range_pairs {B : Type*} [AddCommMonoid B] (f : ℕ → B) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n), f i) =
      ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [add_assoc]

theorem sum_dyadicRank {B : Type*} [AddCommMonoid B] (n : ℕ) (f : ℕ → B) :
    (∑ i : DyadicIndex n, f (dyadicRank n i)) =
      ∑ j ∈ Finset.range (2 ^ n), f j := by
  induction n generalizing f with
  | zero =>
    change (∑ _i : Unit, f 0) = ∑ j ∈ Finset.range 1, f j
    simp
  | succ n ih =>
    change (∑ i : DyadicIndex n × Bool,
      f (2 * dyadicRank n i.1 + if i.2 then 1 else 0)) = _
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [ih (fun j => f (2 * j + 1) + f (2 * j))]
    rw [pow_succ, Nat.mul_comm, sum_range_pairs]
    apply Finset.sum_congr rfl
    intro j _
    exact add_comm _ _

def dyadicPhase (n : ℕ) (i : DyadicIndex n) : ℂ :=
  Complex.exp (((2 * Real.pi * (dyadicRank n i : ℝ) / (2 : ℝ) ^ n : ℝ) : ℂ) *
    Complex.I)

theorem norm_dyadicPhase (n : ℕ) (i : DyadicIndex n) : ‖dyadicPhase n i‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem dyadicPhase_eq_root_pow (n : ℕ) (i : DyadicIndex n) :
    dyadicPhase n i =
      Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℕ)) ^ dyadicRank n i := by
  rw [← Complex.exp_nat_mul]
  unfold dyadicPhase
  congr 1
  push_cast
  ring

theorem sum_dyadicPhase_pow_eq_zero (n k : ℕ) (hk : 0 < k) (hkn : k < 2 ^ n) :
    (∑ i : DyadicIndex n, dyadicPhase n i ^ k) = 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℕ))
  have hz : IsPrimitiveRoot z (2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  have hzk : z ^ k ≠ 1 := by
    intro he
    have hdiv := (hz.pow_eq_one_iff_dvd k).mp he
    exact (not_le_of_gt hkn) (Nat.le_of_dvd hk hdiv)
  have hzpow : (z ^ k) ^ (2 ^ n) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  have hs : (∑ j ∈ Finset.range (2 ^ n), (z ^ k) ^ j) = 0 := by
    have h := geom_sum_mul (z ^ k) (2 ^ n)
    rw [hzpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hzk)
  calc
    (∑ i : DyadicIndex n, dyadicPhase n i ^ k) =
        ∑ i : DyadicIndex n, (z ^ k) ^ dyadicRank n i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [dyadicPhase_eq_root_pow, ← pow_mul, Nat.mul_comm, pow_mul]
    _ = ∑ j ∈ Finset.range (2 ^ n), (z ^ k) ^ j :=
      sum_dyadicRank n (fun j => (z ^ k) ^ j)
    _ = 0 := hs

theorem norm_exp_phase_sub_le (s t : ℝ) :
    ‖Complex.exp ((s : ℂ) * Complex.I) - Complex.exp ((t : ℂ) * Complex.I)‖ ≤
      |s - t| := by
  have he : Complex.exp ((s : ℂ) * Complex.I) - Complex.exp ((t : ℂ) * Complex.I) =
      (Complex.exp (Complex.I * ((s - t : ℝ) : ℂ)) - 1) *
        Complex.exp ((t : ℂ) * Complex.I) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem dyadicPhase_refine_bound (n : ℕ) (i : DyadicIndex (n + 1)) :
    ‖dyadicPhase (n + 1) i - dyadicPhase n i.1‖ ≤
      Real.pi * (1 / 2 : ℝ) ^ n := by
  apply (norm_exp_phase_sub_le _ _).trans
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  change |2 * Real.pi * (dyadicRank (n + 1) i : ℝ) / 2 ^ (n + 1) -
    2 * Real.pi * (dyadicRank n i.1 : ℝ) / 2 ^ n| ≤ _
  cases hb : i.2 <;> simp only [dyadicRank, hb, Bool.false_eq_true, ↓reduceIte,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, pow_succ]
  · have he : 2 * Real.pi * (2 * (dyadicRank n i.1 : ℝ) + 0) / (2 ^ n * 2) -
        2 * Real.pi * (dyadicRank n i.1 : ℝ) / 2 ^ n = 0 := by field_simp; ring
    rw [he, abs_zero]
    positivity
  · have he : 2 * Real.pi * (2 * (dyadicRank n i.1 : ℝ) + 1) / (2 ^ n * 2) -
        2 * Real.pi * (dyadicRank n i.1 : ℝ) / 2 ^ n = Real.pi / 2 ^ n := by
      field_simp
      ring
    rw [he, abs_of_nonneg (by positivity), div_pow, one_pow]
    exact le_of_eq (by ring)

end KadisonSimilarity

end

end OAI
