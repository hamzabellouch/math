import OAI.Geometry.SurfaceImmersion.Geometry.FiniteParametrixPowers

namespace OAI

/-! Explicit terminal derivative orders in finite error profiles. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteParametrix

lemma boundProfile_terminal (L : ℕ) (K C f : ℕ → ℝ) (j m : ℕ) :
    boundProfile L K (fun r => C r * f (r + L)) j m =
      boundProfile L K C j m * f (m + (j + 1) * L) := by
  induction j generalizing m with
  | zero => simp only [boundProfile, zero_add, one_mul]
  | succ j ih =>
    rw [boundProfile, ih, boundProfile]
    have he : m + L + (j + 1) * L = m + (j + 1 + 1) * L := by ring
    rw [he, mul_assoc]

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
