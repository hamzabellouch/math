import OAI.NumberTheory.Ostmann.ZeroDensity.PrimeSumInputs
import OAI.NumberTheory.Ostmann.Quadratic.KernelPrimeCutoffs

namespace OAI

/-! # A concrete diameter and collision budget for large root populations -/

namespace Ostmann

open scoped BigOperators

noncomputable def naturalRootDiameter (m : ℕ) (L : ℝ) : ℕ :=
  ⌈Real.sqrt ((m : ℝ) * Real.exp L)⌉₊

theorem naturalRootDiameter_bounds (m : ℕ) (L η : ℝ) (hm : 0 < m) (hL : 0 ≤ L)
    (hmupper : (m : ℝ) ≤ Real.exp (η * L)) :
    1 ≤ naturalRootDiameter m L ∧
      Real.sqrt ((m : ℝ) * Real.exp L) ≤ naturalRootDiameter m L ∧
      Real.log (naturalRootDiameter m L : ℝ) ≤ Real.log 2 + (1 + η) * L / 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he1 := Real.one_le_exp hL
  have hx1 : (1 : ℝ) ≤ (m : ℝ) * Real.exp L := one_le_mul_of_one_le_of_one_le hm1 he1
  have hr1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) * Real.exp L) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx1
  have hroot : Real.sqrt ((m : ℝ) * Real.exp L) ≤ (naturalRootDiameter m L : ℝ) := Nat.le_ceil _
  have hn1 : (1 : ℝ) ≤ naturalRootDiameter m L := hr1.trans hroot
  refine ⟨by exact_mod_cast hn1, hroot, ?_⟩
  have hceil : (naturalRootDiameter m L : ℝ) ≤ 2 * Real.sqrt ((m : ℝ) * Real.exp L) := by
    have hh : (naturalRootDiameter m L : ℝ) < Real.sqrt ((m : ℝ) * Real.exp L) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    linarith
  have hl := Real.log_le_log (show (0 : ℝ) < naturalRootDiameter m L by linarith) hceil
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by linarith :
    0 < Real.sqrt ((m : ℝ) * Real.exp L))), Real.log_sqrt (by positivity),
    Real.log_mul hm0.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
  have hlogm := (Real.log_le_iff_le_exp hm0).mpr hmupper
  linarith

theorem naturalRootDiameter_dominates (m : ℕ) (L : ℝ) (u : ℤ)
    (hm : 0 < m) (hu : u ≠ 0) :
    Real.sqrt ((m : ℝ) * Real.exp L / |(u : ℝ)|) ≤ naturalRootDiameter m L := by
  have hu1 : (1 : ℝ) ≤ |(u : ℝ)| := by
    have hh : (1 : ℝ) ≤ u.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hu
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  have hnon : 0 ≤ (m : ℝ) * Real.exp L := by positivity
  apply le_trans (Real.sqrt_le_sqrt (div_le_self hnon hu1))
  exact Nat.le_ceil _

/-- Cardinalities at least Q make the two sampling losses at most 2 log 4.
The diameter loss then leaves the manuscript's 1.01L budget. -/
theorem root_population_collision_budget (m Q a b : ℕ) (L η : ℝ)
    (hm : 0 < m) (hQ : 0 < Q) (hL : 1000 ≤ L) (hη : η ≤ 1 / 1000)
    (hmupper : (m : ℝ) ≤ Real.exp (η * L)) (ha : Q ≤ a) (hb : Q ≤ b) :
    2 * Real.log (naturalRootDiameter m L : ℝ) +
      (1 / (a : ℝ) + 1 / (b : ℝ)) * ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) ≤
        (101 / 100 : ℝ) * L := by
  have hd := (naturalRootDiameter_bounds m L η hm (by linarith) hmupper).2.2
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have haR : (Q : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (Q : ℝ) ≤ b := by exact_mod_cast hb
  have hap : (0 : ℝ) < a := hQp.trans_le haR
  have hbp : (0 : ℝ) < b := hQp.trans_le hbR
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsum := prime_log_weight_le Q
  have hfirst : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) / a ≤ Real.log 4 := by
    apply (div_le_iff₀ hap).mpr
    exact hsum.trans (mul_le_mul_of_nonneg_left haR hlog4)
  have hsecond : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) / b ≤ Real.log 4 := by
    apply (div_le_iff₀ hbp).mpr
    exact hsum.trans (mul_le_mul_of_nonneg_left hbR hlog4)
  have hsampling : (1 / (a : ℝ) + 1 / (b : ℝ)) *
      (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ 2 * Real.log 4 := by
    calc
      _ = (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) / a +
          (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) / b := by ring
      _ ≤ _ := by linarith
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4u := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have heta := mul_le_mul_of_nonneg_right hη (show 0 ≤ L by linarith)
  nlinarith

end Ostmann

end OAI
