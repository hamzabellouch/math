import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitAverageFunctions

namespace OAI

/-!
# Bounded coboundary approximations to an orbit observable

The difference between a bounded observable and any one of its finite
orbit averages is an explicit bounded coboundary. This is the uniform
part of the maximal-inequality proof of a common generic set.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*}

def orbitAveragePotential (T : X → X) (f : X → ℝ) (M : ℕ) (x : X) : ℝ :=
  (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, birkhoffSum T f j x

lemma sub_orbit_average_eq_coboundary
    (T : X → X) (f : X → ℝ) (M : ℕ) (hM : M ≠ 0) (x : X) :
    f x - birkhoffAverage ℝ T f M x =
      orbitAveragePotential T f M x - orbitAveragePotential T f M (T x) := by
  have hdiff (j : ℕ) : birkhoffSum T f j x - birkhoffSum T f j (T x) =
      f x - f (T^[j] x) := by
    have h₁ := birkhoffSum_succ_apply T f j x
    have h₂ := birkhoffSum_succ_apply' T f j x
    linarith
  have hc : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  unfold orbitAveragePotential
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [hdiff]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, birkhoffAverage, birkhoffSum, smul_eq_mul]
  field_simp

lemma birkhoffSum_abs_le
    (T : X → X) (f : X → ℝ) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (N : ℕ) (x : X) :
    |birkhoffSum T f N x| ≤ (N : ℝ) * C := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, |f (T^[k] x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, C := Finset.sum_le_sum (fun k _ => hC (T^[k] x))
    _ = _ := by simp

lemma orbitAveragePotential_abs_le
    (T : X → X) (f : X → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, |f x| ≤ C) (M : ℕ) (x : X) :
    |orbitAveragePotential T f M x| ≤ (M : ℝ) * C := by
  by_cases hM : M = 0
  · simp [orbitAveragePotential, hM]
  have hm : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  unfold orbitAveragePotential
  rw [abs_mul, abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, |birkhoffSum T f j x| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hm.le)
    _ ≤ (M : ℝ)⁻¹ * ∑ _j ∈ Finset.range M, (M : ℝ) * C := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hm.le)
      apply Finset.sum_le_sum
      intro j hj
      exact (birkhoffSum_abs_le T f C hC j x).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hj).le) hC0)
    _ = (M : ℝ) * C := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

/-- A bounded coboundary has a uniformly small Cesaro average. -/
lemma orbit_average_coboundary_bound
    (T : X → X) (g : X → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B)
    (N : ℕ) (x : X) :
    |birkhoffAverage ℝ T (fun y => g y - g (T y)) N x| ≤
      (N : ℝ)⁻¹ * (2 * B) := by
  have htel : birkhoffSum T (fun y => g y - g (T y)) N x = g x - g (T^[N] x) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [birkhoffSum_succ_apply, ih, Function.iterate_succ_apply']
        ring
  rw [birkhoffAverage, smul_eq_mul, htel, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have htri : |g x - g (T^[N] x)| ≤ |g x| + |g (T^[N] x)| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (g x) (g (T^[N] x))
  exact mul_le_mul_of_nonneg_left
    (htri.trans (by linarith [hg x, hg (T^[N] x)]))
    (inv_nonneg.mpr (Nat.cast_nonneg N))

end DukePrimeDegree

end

end OAI
