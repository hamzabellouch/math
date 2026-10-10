import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Algebraic final steps for positively curved Einstein four-manifolds

These are the linear-algebra and characteristic-number deductions used in
Sections 1 and 8 of *Positively curved Einstein four-manifolds* (2026).
The geometric hypotheses needed to apply them are kept explicit.
-/

namespace PositiveEinsteinFour

/-- An involution with no nonzero fixed vector is the antipodal linear map.
The proof uses the fixed vector `A x + x`; orthogonality and a spectral theorem
are unnecessary once the sphere action has been linearized. -/
theorem linear_involution_eq_neg_id
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : V →ₗ[ℝ] V)
    (hinvolution : ∀ x, A (A x) = x)
    (hfixed : ∀ x, A x = x → x = 0) :
    A = -LinearMap.id := by
  ext x
  have hsum : A (A x + x) = A x + x := by
    rw [map_add, hinvolution, add_comm]
  have hzero := hfixed (A x + x) hsum
  simpa using eq_neg_of_add_eq_zero_left hzero

/-- A linear involution acting freely on the unit sphere is antipodal. -/
theorem linear_involution_eq_neg_id_of_sphere_free
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →ₗ[ℝ] V)
    (hinvolution : ∀ x, A (A x) = x)
    (hfree : ∀ x, ‖x‖ = 1 → A x ≠ x) :
    A = -LinearMap.id := by
  apply linear_involution_eq_neg_id A hinvolution
  intro x hfixed
  by_contra hx
  apply hfree ((‖x‖⁻¹ : ℝ) • x) (norm_smul_inv_norm hx)
  rw [map_smul, hfixed]

/-- The characteristic identities, the Weyl gap, and the strict lower volume
bound in the exceptional moment-three case force the sole surviving harmonic
count to be one. Volume is divided by `π²`; `moment` denotes the normalized
second moment of the nonzero block. This is Proposition 8.2's numerical step. -/
theorem remaining_harmonic_count
    (n : ℕ) (volume moment : ℝ)
    (hvolume_pos : 0 < volume)
    (hgap : 1 ≤ moment)
    (hmoment_lt : moment < 4)
    (hcharacteristic : volume = (8 - 2 * (n : ℝ)) / 3)
    (hsignature : moment * volume = 2 * (n : ℝ))
    (hvolume_exceptional : moment = 3 → 4 / 3 < volume) :
    n = 1 ∧ moment = 1 ∧ volume = 2 := by
  have hn_pos : 0 < (n : ℝ) := by nlinarith
  have hn_nat_pos : 0 < n := by exact_mod_cast hn_pos
  have hn_nat_lt : n < 3 := by
    by_contra hnot
    have hn_ge : 3 ≤ n := by omega
    have hn_real_ge : 3 ≤ (n : ℝ) := by exact_mod_cast hn_ge
    have hmoment_volume : moment * volume < 4 * volume :=
      mul_lt_mul_of_pos_right hmoment_lt hvolume_pos
    nlinarith
  have hn_cases : n = 1 ∨ n = 2 := by omega
  have hn : n = 1 := by
    rcases hn_cases with hn | hn
    · exact hn
    · subst n
      norm_num at hcharacteristic hsignature
      have hmoment : moment = 3 := by nlinarith
      have := hvolume_exceptional hmoment
      linarith
  subst n
  norm_num at hcharacteristic hsignature
  refine ⟨rfl, ?_, ?_⟩
  · nlinarith
  · linarith

/-- The normalized eigenvalues of a trace-free symmetric three-by-three
matrix have the parameter range and cubic invariant used in Section 2.
Here `-r` is the least eigenvalue and the squared Hilbert--Schmidt norm is six.
This elementary form needs neither eigenvector choices nor a square root. -/
theorem normalized_eigenvalue_parameter
    (r s t : ℝ)
    (htrace : -r + s + t = 0)
    (hnorm : r ^ 2 + s ^ 2 + t ^ 2 = 6)
    (hs : -r ≤ s) (ht : -r ≤ t) :
    1 ≤ r ∧ r ≤ 2 ∧ s * t = r ^ 2 - 3 ∧
      ((-r) ^ 3 + s ^ 3 + t ^ 3) / 6 = (3 * r - r ^ 3) / 2 := by
  have ht_eq : t = r - s := by linarith
  subst t
  have hr_nonneg : 0 ≤ r := by linarith
  have hproduct : s * (r - s) = r ^ 2 - 3 := by nlinarith
  have hr_lower : 1 ≤ r := by
    have hpositive_product : 0 ≤ (s + r) * (r - s + r) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hr_upper : r ≤ 2 := by
    nlinarith [sq_nonneg (s - (r - s))]
  refine ⟨hr_lower, hr_upper, hproduct, ?_⟩
  have hcube : (-r) ^ 3 + s ^ 3 + (r - s) ^ 3 = -3 * r * (s * (r - s)) := by
    ring
  rw [hcube, hproduct]
  ring

end PositiveEinsteinFour

end OAI
