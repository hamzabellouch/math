import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactBaseSeparation

namespace OAI

/-! The prescribed nineteen-link gadgets retain the nonlink separation of the
base shapes. All estimates concern the actual coordinate constructions. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactPoint_axis_dist (x x' : ℝ) :
    dist (contactPoint x 0) (contactPoint x' 0) = |x - x'| := by
  have h := contactPoint_dist_sq x 0 x' 0
  nlinarith [sq_abs (x - x'), abs_nonneg (x - x'),
    show 0 ≤ dist (contactPoint x 0) (contactPoint x' 0) from dist_nonneg]

theorem contactPoint_vertical_dist (x y y' : ℝ) :
    dist (contactPoint x y) (contactPoint x y') = |y - y'| := by
  have h := contactPoint_dist_sq x y x y'
  nlinarith [sq_abs (y - y'), abs_nonneg (y - y'),
    show 0 ≤ dist (contactPoint x y) (contactPoint x y') from dist_nonneg]

theorem contactGadgetOrigin_near (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance) :
    dist (contactPoint (contactGadgetRightOrigin negative central) 0)
      (contactPoint (contactGadgetRightOrigin negative 1) 0) ≤ contactLengthTolerance := by
  rw [contactPoint_axis_dist]
  cases negative
  · apply abs_le.mpr
    simp only [contactGadgetRightOrigin, Bool.false_eq_true, ite_false]
    constructor <;> linarith
  · norm_num [contactGadgetRightOrigin, contactLengthTolerance]

/-- The complete actual gadget, including the central partner, stays inside
the same fixed separation guard as the independently adjusted paths. -/
theorem contactGadgetPosition_near (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance)
    (leftLengths rightLengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths k)
    (hl' : ∀ k < 9, leftLengths k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths k)
    (hr' : ∀ k < 9, rightLengths k ≤ 1 + contactLengthTolerance)
    {leftHeight rightHeight : ℝ}
    (hleftHeight : leftHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hrightHeight : rightHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative))) (x : ContactGadgetSite) :
    dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight x)
      (contactBaseGadgetPosition negative x) < 1 / 20 := by
  have hs := contactGadgetSlope_bounds negative
  rcases x with i | (i | ⟨⟩)
  · exact adjustedContactVertex_near hs.1 hs.2 hleftHeight leftLengths hl hl'
      (show i.val ≤ 9 by have := i.isLt; omega)
  · have hpath := adjustedContactVertex_displacement hs.1 hs.2 hrightHeight rightLengths hr hr'
      (show i.val + 1 ≤ 9 by have := i.isLt; omega)
    have horigin := contactGadgetOrigin_near negative hc hc'
    have hdist := dist_add_add_le (contactPoint (contactGadgetRightOrigin negative central) 0)
      (adjustedContactVertex rightLengths rightHeight (i.val + 1))
      (contactPoint (contactGadgetRightOrigin negative 1) 0)
      (contactPathVertex (contactGadgetSlope negative) (i.val + 1))
    change dist (contactPoint (contactGadgetRightOrigin negative central) 0 +
      adjustedContactVertex rightLengths rightHeight (i.val + 1))
      (contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (i.val + 1)) < 1 / 20
    unfold contactLengthTolerance at horigin
    linarith
  · cases negative
    · change dist (contactPoint ((17 + central) / 2) 0) (contactPoint 9 0) < 1 / 20
      have h := contactGadgetOrigin_near false hc hc'
      norm_num [contactGadgetRightOrigin, contactLengthTolerance] at h
      linarith
    · change dist (contactPoint (17 / 2) central) (contactPoint (17 / 2) 1) < 1 / 20
      rw [contactPoint_vertical_dist]
      have habs : |central - 1| ≤ contactLengthTolerance := abs_le.mpr ⟨by linarith, by linarith⟩
      exact habs.trans_lt (by norm_num [contactLengthTolerance])

/-- The actual variable-link gadget retains distance greater than1.2 for
every distinct pair which is not one of its nineteen links. -/
theorem contactGadget_nonlink_separation (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance)
    (leftLengths rightLengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths k)
    (hl' : ∀ k < 9, leftLengths k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths k)
    (hr' : ∀ k < 9, rightLengths k ≤ 1 + contactLengthTolerance)
    {leftHeight rightHeight : ℝ}
    (hleftHeight : leftHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hrightHeight : rightHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (x y : ContactGadgetSite) (hne : x ≠ y) (hlink : ¬ contactGadgetLinked negative x y) :
    6 / 5 < dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight x)
      (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight y) := by
  have hnear := contactGadgetPosition_near negative hc hc' leftLengths rightLengths hl hl' hr hr'
    hleftHeight hrightHeight
  apply contact_separation_stable (contactBaseGadgetPosition negative x)
    (contactBaseGadgetPosition negative y) _ _ (contactBaseGadget_nonlink_separation negative x y hne hlink)
  · rw [dist_comm]
    exact (hnear x).le
  · rw [dist_comm]
    exact (hnear y).le

end ContinuumCoulomb

end

end OAI
