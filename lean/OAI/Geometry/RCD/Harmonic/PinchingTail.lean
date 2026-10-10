import OAI.Geometry.RCD.Harmonic.PinchingEnvelope

namespace OAI

/-! # Inward square-root tails are controlled by the summable envelope

Only the defect itself needs to be summable. Its square root need not be.
The extra decay from the radii controls the inward tail of affine constants.
-/

open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

theorem geometric_sqrt_tail_le {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 ≤ τ) (hτρ : τ < Real.sqrt ρ)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P) (i d : ℕ) :
    Summable (fun k : ℕ => τ ^ k * Real.sqrt (P (i + d + k))) ∧
      (∑' k : ℕ, τ ^ k * Real.sqrt (P (i + d + k))) ≤
        (1 - τ / Real.sqrt ρ)⁻¹ *
          (Real.sqrt (symmetricDefect ρ P i) / (Real.sqrt ρ) ^ d) := by
  let E := symmetricDefect ρ P i
  let s := Real.sqrt ρ
  have hs : 0 < s := Real.sqrt_pos.mpr hρ
  have hE : 0 ≤ E := symmetricDefect_nonneg hρ.le hP i
  have hratio0 : 0 ≤ τ / s := div_nonneg hτ hs.le
  have hratio1 : τ / s < 1 := (div_lt_one hs).mpr hτρ
  have hbound (k : ℕ) : τ ^ k * Real.sqrt (P (i + d + k)) ≤
      (τ / s) ^ k * (Real.sqrt E / s ^ d) := by
    have hterm := term_le_symmetricDefect hρ.le hρ1 hP hPs i (i + d + k)
    have hdist : Nat.dist i (i + d + k) = d + k := by
      rw [Nat.dist_eq_sub_of_le (by omega)]
      omega
    rw [hdist] at hterm
    have hsquare : (s ^ (d + k) * Real.sqrt (P (i + d + k))) ^ 2 ≤ (Real.sqrt E) ^ 2 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm (d + k) 2, pow_mul,
        show s ^ 2 = ρ from Real.sq_sqrt hρ.le, Real.sq_sqrt (hP _), Real.sq_sqrt hE]
      exact hterm
    have hroot : s ^ (d + k) * Real.sqrt (P (i + d + k)) ≤ Real.sqrt E :=
      (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsquare
    have hdiv : Real.sqrt (P (i + d + k)) ≤ Real.sqrt E / s ^ (d + k) :=
      (le_div_iff₀ (pow_pos hs _)).mpr (by simpa only [mul_comm] using hroot)
    calc
      _ ≤ τ ^ k * (Real.sqrt E / s ^ (d + k)) :=
        mul_le_mul_of_nonneg_left hdiv (pow_nonneg hτ _)
      _ = _ := by rw [div_pow, pow_add]; field_simp
  have hg : Summable (fun k : ℕ => (τ / s) ^ k * (Real.sqrt E / s ^ d)) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_right _
  have ht := Summable.of_nonneg_of_le (fun k => by positivity) hbound hg
  refine ⟨ht, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, (τ / s) ^ k * (Real.sqrt E / s ^ d) := ht.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_right, tsum_geometric_of_lt_one hratio0 hratio1]

end RegularPointCoordinates

end

end OAI
