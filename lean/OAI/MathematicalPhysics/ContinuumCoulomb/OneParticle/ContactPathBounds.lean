import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactStrips

namespace OAI

/-! Coordinate bounds for the two explicit paths. These imply the fixed strip
conditions used to separate gadgets throughout an arbitrarily large lattice. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem contactSlopeHeight_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    0 ≤ contactSlopeHeight c ∧ contactSlopeHeight c ≤ 2 / 3 := by
  have hs := contactSlopeHeight_sq (by linarith : -1 ≤ c) (by linarith : c ≤ 1)
  have hn : 0 ≤ contactSlopeHeight c := Real.sqrt_nonneg _
  exact ⟨hn, by nlinarith⟩

theorem contactPath_transverse_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : k ≤ 9) :
    0 ≤ contactPathVertex c k 1 ∧ contactPathVertex c k 1 ≤ 4 / 3 := by
  have hs := contactSlopeHeight_bounds hc hc'
  interval_cases k <;> norm_num [contactPathVertex, Finset.sum_range_succ, contactStepY,
    contactPoint] <;> (try constructor) <;> linarith

theorem contactPath_axial_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (_hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : k ≤ 9) :
    0 ≤ contactPathVertex c k 0 ∧ contactPathVertex c k 0 ≤ 5 + 4 * c := by
  interval_cases k <;> norm_num [contactPathVertex, Finset.sum_range_succ, contactStepX,
    contactPoint] <;> (try constructor) <;> linarith

theorem contactPath_internal_axial_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (_hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 8) :
    1 ≤ contactPathVertex c k 0 ∧ contactPathVertex c k 0 ≤ 4 + 4 * c := by
  interval_cases k <;> norm_num [contactPathVertex, Finset.sum_range_succ, contactStepX,
    contactPoint] <;> (try constructor) <;> linarith

theorem contactPath_off_axis_bounds {c : ℝ} (hc : 3 / 4 ≤ c) (_hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : k ≤ 9) (hy : contactPathVertex c k 1 ≠ 0) :
    11 / 4 ≤ contactPathVertex c k 0 ∧ contactPathVertex c k 0 ≤ 9 / 4 + 4 * c := by
  interval_cases k <;> norm_num [contactPathVertex, Finset.sum_range_succ, contactStepY, contactPoint] at hy
  all_goals norm_num [contactPathVertex, Finset.sum_range_succ, contactStepX, contactPoint]
  all_goals constructor <;> linarith

/-- Left-path internal sites and its central endpoint satisfy the common
length-17 strip bounds. -/
def leftContactStripSite (c : ℝ) (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 9) : ContactStripSite where
  axial := contactPathVertex c k 0
  transverse := contactPathVertex c k 1
  axial_lower := by
    by_cases h : k = 9
    · subst k
      rw [contactPathVertex_end, contactPoint_zero]
      linarith
    · exact (contactPath_internal_axial_bounds hc hc' hk (by omega)).1
  axial_upper := (contactPath_axial_bounds hc hc' hk').2.trans (by linarith)
  transverse_lower := (contactPath_transverse_bounds hc hc' hk').1
  transverse_upper := (contactPath_transverse_bounds hc hc' hk').2
  off_axis_lower := fun h => (contactPath_off_axis_bounds hc hc' hk' h).1
  off_axis_upper := fun h => (contactPath_off_axis_bounds hc hc' hk' h).2.trans (by linarith)

/-- Right-path internal sites use an origin chosen so their far endpoint is17. -/
def rightContactStripSite (c origin : ℝ) (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (horigin : origin + (5 + 4 * c) = 17)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 8) : ContactStripSite where
  axial := origin + contactPathVertex c k 0
  transverse := contactPathVertex c k 1
  axial_lower := by
    have := (contactPath_internal_axial_bounds hc hc' hk hk').1
    linarith
  axial_upper := by
    have := (contactPath_internal_axial_bounds hc hc' hk hk').2
    linarith
  transverse_lower := (contactPath_transverse_bounds hc hc' (by omega : k ≤ 9)).1
  transverse_upper := (contactPath_transverse_bounds hc hc' (by omega : k ≤ 9)).2
  off_axis_lower := by
    intro hy
    have := (contactPath_off_axis_bounds hc hc' (by omega : k ≤ 9) hy).1
    linarith
  off_axis_upper := by
    intro hy
    have := (contactPath_off_axis_bounds hc hc' (by omega : k ≤ 9) hy).2
    linarith

end ContinuumCoulomb

end

end OAI
