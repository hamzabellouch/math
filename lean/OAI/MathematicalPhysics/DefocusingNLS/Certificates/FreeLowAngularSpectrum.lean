import OAI.MathematicalPhysics.DefocusingNLS.Certificates.UniformOutgoingCount

namespace OAI

/-! # The low angular outgoing counts on the manuscript's parameter disk -/

open Set

namespace DefocusingNLS

/-- The exact disk in equation `free:parameter-disk`; terminating decimals are
represented as rational numbers. -/
def freeMatchingDisk : Set (ℝ × ℝ) :=
  {p | (p.1 - 33477606871236 / 100000000000000) ^ 2 +
    (p.2 - 270506819293654 / 100000000000000) ^ 2 ≤ (1 / 100000000 : ℝ) ^ 2}

theorem freeMatchingDisk_subset_certificate_box {b Z : ℝ}
    (h : (b, Z) ∈ freeMatchingDisk) :
    |100000000 * b - 33477607| ≤ 2 ∧ |100000000 * Z - 270506819| ≤ 2 := by
  change (b - 33477606871236 / 100000000000000) ^ 2 +
    (Z - 270506819293654 / 100000000000000) ^ 2 ≤ (1 / 100000000 : ℝ) ^ 2 at h
  have hb : |b - 33477606871236 / 100000000000000| ≤ (1 / 100000000 : ℝ) := by
    nlinarith [sq_nonneg (Z - 270506819293654 / 100000000000000),
      sq_abs (b - 33477606871236 / 100000000000000),
      abs_nonneg (b - 33477606871236 / 100000000000000)]
  have hZ : |Z - 270506819293654 / 100000000000000| ≤ (1 / 100000000 : ℝ) := by
    nlinarith [sq_nonneg (b - 33477606871236 / 100000000000000),
      sq_abs (Z - 270506819293654 / 100000000000000),
      abs_nonneg (Z - 270506819293654 / 100000000000000)]
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  obtain ⟨hZ₁, hZ₂⟩ := abs_le.mp hZ
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

noncomputable def closedCountingHalfPlaneZeroCount (f : ℂ → ℂ) : ℕ∞ :=
  ∑' z : {z : ℂ | -(1 / 32 : ℝ) ≤ z.re}, analyticOrderAt f z.1

theorem spectralSlowDeterminant_left_ne_zero (ell : Fin 4) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (z : ℂ) (hz : z.re = -(1 / 32 : ℝ)) : spectralSlowDeterminant ell b Z z ≠ 0 := by
  have hZ0 : Z ≠ 0 := by intro h; norm_num [h] at hZ
  exact spectralSlowDeterminant_ne_zero_of_endpoint ell b Z z hZ0 hz.ge
    (spectralHomotopyDeterminant_left ell b Z 1 z hb hZ (by norm_num) le_rfl hz)

theorem closedCountingHalfPlaneZeroCount_eq_open (ell : Fin 4) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    closedCountingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z) =
      countingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z) := by
  classical
  unfold closedCountingHalfPlaneZeroCount countingHalfPlaneZeroCount
  rw [tsum_subtype, tsum_subtype]
  apply tsum_congr
  intro z
  by_cases ho : -(1 / 32 : ℝ) < z.re
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left ho, ite_eq_left ho.le]
  · by_cases hc : -(1 / 32 : ℝ) ≤ z.re
    · have he : z.re = -(1 / 32 : ℝ) := le_antisymm (le_of_not_gt ho) hc
      have hz : analyticOrderAt (spectralSlowDeterminant ell b Z) z = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (spectralSlowDeterminant_left_ne_zero ell b Z hb hZ z he))
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hc, ite_eq_right ho, hz]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hc, ite_eq_right ho]

/-- The low modes of Proposition `free:main`, on its exact disk and closed
counting half-plane. -/
theorem free_low_angular_count (hR : RectangleRouche) (ell : Fin 4) (b Z : ℝ)
    (h : (b, Z) ∈ freeMatchingDisk) :
    closedCountingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z) =
      (SeparatorArithmetic.positiveRootCount ell : ℕ∞) := by
  obtain ⟨hb, hZ⟩ := freeMatchingDisk_subset_certificate_box h
  exact (closedCountingHalfPlaneZeroCount_eq_open ell b Z hb hZ).trans
    (outgoing_halfPlane_count hR ell b Z hb hZ)

end DefocusingNLS

end OAI
