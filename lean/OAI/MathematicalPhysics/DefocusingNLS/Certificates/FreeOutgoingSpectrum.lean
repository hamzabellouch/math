import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeHighAngularSpectrum

namespace OAI

/-! The complete free outgoing count on the manuscript's parameter disk. -/

namespace DefocusingNLS

def freeOutgoingCount (ell : ℕ) : ℕ := if ell=0 then 2 else if ell=1 then 1 else 0

theorem free_high_angular_count (ell : ℕ) (b Z : ℝ) (hell : 4 ≤ ell)
    (hD : (b,Z) ∈ freeMatchingDisk) :
    closedCountingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z)=0 := by
  unfold closedCountingHalfPlaneZeroCount
  have hz : ∀ z : {z : ℂ | -(1/32 : ℝ) ≤ z.re},
      analyticOrderAt (spectralSlowDeterminant ell b Z) z.1 = 0 := by
    intro z
    exact analyticOrderAt_eq_zero.mpr (Or.inr
      (free_high_angular_nonzero_on_disk ell b Z z hell hD z.2))
  simp only [hz,tsum_zero]

theorem free_outgoing_count (hR : RectangleRouche) (ell : ℕ) (b Z : ℝ)
    (hD : (b,Z) ∈ freeMatchingDisk) :
    closedCountingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z)=
      (freeOutgoingCount ell : ℕ∞) := by
  by_cases hl : ell < 4
  · have h := free_low_angular_count hR ⟨ell,hl⟩ b Z hD
    interval_cases ell <;> simpa [freeOutgoingCount,SeparatorArithmetic.positiveRootCount] using h
  · have he : 4 ≤ ell := by omega
    rw [free_high_angular_count ell b Z he hD]
    simp [freeOutgoingCount,show ell≠0 by omega,show ell≠1 by omega]

end DefocusingNLS

end OAI
