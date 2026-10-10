import OAI.Analysis.CircleDomains.Topology.CutoffStaircase

namespace OAI

/-!
# Wedge estimate for cutoff staircase coordinates

The common cutoff differential makes the quadratic error term vanish.
The remaining terms have exactly the bounds used before taking independent
shift expectations in the finite-transfer construction.
-/

namespace CircleDomainRigidity.FiniteTransfer

def planarWedge (v w : ℝ × ℝ) : ℝ := v.1 * w.2 - v.2 * w.1

/-- The two error covectors have the same direction, so their wedge is zero. -/
theorem planarWedge_cutoff_expansion (u v c : ℝ × ℝ) (q p r s : ℝ) :
    planarWedge (q • u + r • c) (p • v + s • c) =
      q * p * planarWedge u v + q * s * planarWedge u c + r * p * planarWedge c v := by
  simp only [planarWedge, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Pointwise bound for the wedge of two modified coordinate gradients. -/
theorem abs_planarWedge_cutoff_le (u v c : ℝ × ℝ) {q p r s h : ℝ}
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hr : |r| ≤ h) (hs : |s| ≤ h) :
    |planarWedge (q • u + r • c) (p • v + s • c)| ≤
      q * p * |planarWedge u v| + h * q * |planarWedge u c| +
        h * p * |planarWedge c v| := by
  rw [planarWedge_cutoff_expansion]
  calc
    |q * p * planarWedge u v + q * s * planarWedge u c + r * p * planarWedge c v| ≤
        |q * p * planarWedge u v| + |q * s * planarWedge u c| +
          |r * p * planarWedge c v| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = q * p * |planarWedge u v| + |s| * q * |planarWedge u c| +
          |r| * p * |planarWedge c v| := by
      simp only [abs_mul, abs_of_nonneg hq, abs_of_nonneg hp]
      ring
    _ ≤ _ := by
      gcongr

end CircleDomainRigidity.FiniteTransfer

end OAI
