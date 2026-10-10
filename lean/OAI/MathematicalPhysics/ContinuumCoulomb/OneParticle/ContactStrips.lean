import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactTemplates

namespace OAI

/-! Uniform separation of contacts from different lattice edges. The estimates
use only fixed strip bounds, so the lattice size never enters their constants. -/

noncomputable section
namespace ContinuumCoulomb

/-- Coordinates of an internal site in an oriented length-17 lattice edge.
Off-axis sites stay farther from both original endpoints. -/
structure ContactStripSite where
  axial : ℝ
  transverse : ℝ
  axial_lower : 1 ≤ axial
  axial_upper : axial ≤ 16
  transverse_lower : 0 ≤ transverse
  transverse_upper : transverse ≤ 4 / 3
  off_axis_lower : transverse ≠ 0 → 11 / 4 ≤ axial
  off_axis_upper : transverse ≠ 0 → axial ≤ 57 / 4

def horizontalContact (a b : ℤ) (p : ContactStripSite) : ContactPoint :=
  contactPoint (17 * a + p.axial) (17 * b + p.transverse)

def verticalContact (a b : ℤ) (p : ContactStripSite) : ContactPoint :=
  contactPoint (17 * a - p.transverse) (17 * b + p.axial)

theorem contact_interval_lattice_distance {x margin : ℝ}
    (hx : margin ≤ x) (hx' : x ≤ 17 - margin) (k : ℤ) :
    margin ≤ |x - 17 * k| := by
  by_cases hk : k ≤ 0
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    exact (le_abs_self _).trans' (by linarith)
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    exact (neg_le_abs _).trans' (by linarith)

theorem contactPoint_coordinate_le_dist (p q : ContactPoint) (i : Fin 2) :
    |p i - q i| ≤ dist p q := by
  have hdist := EuclideanSpace.dist_sq_eq p q
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hdist
  fin_cases i
  · change |p 0 - q 0| ≤ dist p q
    nlinarith [sq_nonneg (p 1 - q 1), abs_nonneg (p 0 - q 0),
      sq_abs (p 0 - q 0), show 0 ≤ dist p q from dist_nonneg]
  · change |p 1 - q 1| ≤ dist p q
    nlinarith [sq_nonneg (p 0 - q 0), abs_nonneg (p 1 - q 1),
      sq_abs (p 1 - q 1), show 0 ≤ dist p q from dist_nonneg]

/-- Perpendicular gadgets retain the paper's 1.4 nonlink margin. -/
theorem perpendicularContact_separation (a b c d : ℤ) (p q : ContactStripSite) :
    7 / 5 < dist (horizontalContact a b p) (verticalContact c d q) := by
  by_cases hp : p.transverse = 0
  · by_cases hq : q.transverse = 0
    · have hx := contact_interval_lattice_distance p.axial_lower
        (show p.axial ≤ 17 - (1 : ℝ) by linarith [p.axial_upper]) (c - a)
      have hy := contact_interval_lattice_distance q.axial_lower
        (show q.axial ≤ 17 - (1 : ℝ) by linarith [q.axial_upper]) (b - d)
      have hdist := contactPoint_dist_sq
        (17 * a + p.axial) (17 * b + p.transverse)
        (17 * c - q.transverse) (17 * d + q.axial)
      have hx' : 1 ≤ |17 * (a : ℝ) + p.axial - (17 * c - q.transverse)| := by
        push_cast at hx
        rw [hq, sub_zero]
        convert hx using 1
        congr 1
        ring
      have hy' : 1 ≤ |17 * (b : ℝ) + p.transverse - (17 * d + q.axial)| := by
        push_cast at hy
        rw [hp]
        have hneg : 17 * (b : ℝ) + 0 - (17 * d + q.axial) =
            -(q.axial - 17 * ((b : ℝ) - d)) := by ring
        rw [hneg, abs_neg]
        exact hy
      have hx2 : 1 ≤ (17 * (a : ℝ) + p.axial - (17 * c - q.transverse)) ^ 2 := by
        nlinarith [sq_abs (17 * (a : ℝ) + p.axial - (17 * c - q.transverse))]
      have hy2 : 1 ≤ (17 * (b : ℝ) + p.transverse - (17 * d + q.axial)) ^ 2 := by
        nlinarith [sq_abs (17 * (b : ℝ) + p.transverse - (17 * d + q.axial))]
      change dist (horizontalContact a b p) (verticalContact c d q) ^ 2 = _ at hdist
      nlinarith [show 0 ≤ dist (horizontalContact a b p) (verticalContact c d q) from dist_nonneg]
    · have hy := contact_interval_lattice_distance (q.off_axis_lower hq)
        (show q.axial ≤ 17 - (11 / 4 : ℝ) by linarith [q.off_axis_upper hq]) (b - d)
      push_cast at hy
      have htriangle := abs_add_le (q.axial - 17 * ((b : ℝ) - d) - p.transverse) p.transverse
      have htrans : |p.transverse| ≤ 4 / 3 := by
        rw [abs_of_nonneg p.transverse_lower]
        exact p.transverse_upper
      have hcoordinate := contactPoint_coordinate_le_dist
        (horizontalContact a b p) (verticalContact c d q) 1
      change |17 * (b : ℝ) + p.transverse - (17 * d + q.axial)| ≤ _ at hcoordinate
      have hneg : q.axial - 17 * ((b : ℝ) - d) - p.transverse =
          -(17 * (b : ℝ) + p.transverse - (17 * d + q.axial)) := by ring
      rw [hneg, abs_neg] at htriangle
      have hsum : -(17 * (b : ℝ) + p.transverse - (17 * d + q.axial)) + p.transverse =
          q.axial - 17 * ((b : ℝ) - d) := by ring
      rw [hsum] at htriangle
      linarith
  · have hx := contact_interval_lattice_distance (p.off_axis_lower hp)
      (show p.axial ≤ 17 - (11 / 4 : ℝ) by linarith [p.off_axis_upper hp]) (c - a)
    push_cast at hx
    have htriangle := abs_sub_le (p.axial - 17 * ((c : ℝ) - a) + q.transverse) (0 : ℝ) q.transverse
    simp only [sub_zero, zero_sub, abs_neg] at htriangle
    have htrans : |q.transverse| ≤ 4 / 3 := by
      rw [abs_of_nonneg q.transverse_lower]
      exact q.transverse_upper
    have hcoordinate := contactPoint_coordinate_le_dist
      (horizontalContact a b p) (verticalContact c d q) 0
    change |17 * (a : ℝ) + p.axial - (17 * c - q.transverse)| ≤ _ at hcoordinate
    have hdiff : p.axial - 17 * ((c : ℝ) - a) + q.transverse - q.transverse =
        p.axial - 17 * ((c : ℝ) - a) := by ring
    rw [hdiff] at htriangle
    have hsum : p.axial - 17 * ((c : ℝ) - a) + q.transverse =
        17 * (a : ℝ) + p.axial - (17 * c - q.transverse) := by ring
    rw [hsum] at htriangle
    linarith

/-- Internal points from distinct collinear length-17 intervals are at least
2 apart in their axial projection. -/
theorem contact_interval_separation (a c : ℤ) (hne : a ≠ c) {x y : ℝ}
    (hx : 1 ≤ x) (hx' : x ≤ 16) (hy : 1 ≤ y) (hy' : y ≤ 16) :
    2 ≤ |17 * (a : ℝ) + x - (17 * c + y)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (a : ℝ) + 1 ≤ c := by exact_mod_cast (show a + 1 ≤ c by omega)
    exact (neg_le_abs _).trans' (by linarith)
  · have h' : (c : ℝ) + 1 ≤ a := by exact_mod_cast (show c + 1 ≤ a by omega)
    exact (le_abs_self _).trans' (by linarith)

theorem contact_parallel_line_separation (b d : ℤ) (hne : b ≠ d) {x y : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 4 / 3) (hy : 0 ≤ y) (hy' : y ≤ 4 / 3) :
    47 / 3 ≤ |17 * (b : ℝ) + x - (17 * d + y)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (b : ℝ) + 1 ≤ d := by exact_mod_cast (show b + 1 ≤ d by omega)
    exact (neg_le_abs _).trans' (by linarith)
  · have h' : (d : ℝ) + 1 ≤ b := by exact_mod_cast (show d + 1 ≤ b by omega)
    exact (le_abs_self _).trans' (by linarith)

/-- Parallel gadgets from distinct oriented lattice edges do not interfere. -/
theorem horizontalContact_separation (a b c d : ℤ)
    (hne : (a, b) ≠ (c, d)) (p q : ContactStripSite) :
    7 / 5 < dist (horizontalContact a b p) (horizontalContact c d q) := by
  by_cases hb : b = d
  · have ha : a ≠ c := by intro ha; exact hne (Prod.ext ha hb)
    have h := contact_interval_separation a c ha p.axial_lower p.axial_upper q.axial_lower q.axial_upper
    have hdist := contactPoint_coordinate_le_dist (horizontalContact a b p) (horizontalContact c d q) 0
    change |17 * (a : ℝ) + p.axial - (17 * c + q.axial)| ≤ _ at hdist
    linarith
  · have h := contact_parallel_line_separation b d hb p.transverse_lower p.transverse_upper
      q.transverse_lower q.transverse_upper
    have hdist := contactPoint_coordinate_le_dist (horizontalContact a b p) (horizontalContact c d q) 1
    change |17 * (b : ℝ) + p.transverse - (17 * d + q.transverse)| ≤ _ at hdist
    linarith

end ContinuumCoulomb

end

end OAI
