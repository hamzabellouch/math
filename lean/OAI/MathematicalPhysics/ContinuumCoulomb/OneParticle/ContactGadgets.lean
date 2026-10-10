import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactDisplacement

namespace OAI

/-! The two signed-edge contact gadgets. Each has twenty sites, nineteen
links, fixed original endpoints, and independently prescribed link lengths.
A negative input sign places the central partner off the backbone. -/

noncomputable section
namespace ContinuumCoulomb

abbrev ContactGadgetSite := Fin 10 ⊕ (Fin 9 ⊕ Unit)

def contactGadgetSlope (negative : Bool) : ℝ := if negative then 7 / 8 else 3 / 4

def contactGadgetSpan (negative : Bool) (central : ℝ) : ℝ :=
  if negative then 17 / 2 else (17 - central) / 2

def contactGadgetRightOrigin (negative : Bool) (central : ℝ) : ℝ :=
  if negative then 17 / 2 else (17 + central) / 2

def contactGadgetSide : ContactGadgetSite := Sum.inr (Sum.inr ())

def contactGadgetRightNode (negative : Bool) (k : Fin 10) : ContactGadgetSite :=
  if hk : k = 0 then
    if negative then Sum.inl 9 else contactGadgetSide
  else Sum.inr (Sum.inl ⟨k.val - 1, by have := k.isLt; omega⟩)

def contactGadgetPosition (negative : Bool) (central : ℝ)
    (leftLengths rightLengths : ℕ → ℝ) (leftHeight rightHeight : ℝ) :
    ContactGadgetSite → ContactPoint :=
  Sum.elim (fun k => adjustedContactVertex leftLengths leftHeight k.val)
    (Sum.elim (fun k => contactPoint (contactGadgetRightOrigin negative central) 0 +
      adjustedContactVertex rightLengths rightHeight (k.val + 1))
      (fun _ => if negative then contactPoint (17 / 2) central
        else contactPoint (contactGadgetRightOrigin negative central) 0))

theorem contactGadgetSlope_bounds (negative : Bool) :
    3 / 4 ≤ contactGadgetSlope negative ∧ contactGadgetSlope negative ≤ 7 / 8 := by
  cases negative <;> norm_num [contactGadgetSlope]

theorem contactGadgetSpan_bounds (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance) :
    5 + 4 * contactGadgetSlope negative - contactLengthTolerance ≤ contactGadgetSpan negative central ∧
      contactGadgetSpan negative central ≤ 5 + 4 * contactGadgetSlope negative + contactLengthTolerance := by
  cases negative
  · simp only [contactGadgetSlope, contactGadgetSpan, Bool.false_eq_true, ite_false]
    constructor <;> linarith
  · norm_num [contactGadgetSlope, contactGadgetSpan, contactLengthTolerance]

theorem contactGadgetRightNode_position (negative : Bool) (central : ℝ)
    (leftLengths rightLengths : ℕ → ℝ) (leftHeight rightHeight : ℝ)
    (hleft : adjustedContactSpan leftLengths leftHeight = contactGadgetSpan negative central)
    (k : Fin 10) :
    contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (contactGadgetRightNode negative k) =
      contactPoint (contactGadgetRightOrigin negative central) 0 +
        adjustedContactVertex rightLengths rightHeight k.val := by
  by_cases hk : k = 0
  · subst k
    rw [contactGadgetRightNode, dite_eq_left rfl]
    cases negative
    · simp [contactGadgetPosition, contactGadgetSide, adjustedContactVertex, contactPoint]
    · change adjustedContactVertex leftLengths leftHeight 9 = contactPoint (17 / 2) 0 +
        adjustedContactVertex rightLengths rightHeight 0
      rw [adjustedContactVertex_end, hleft]
      simp [contactGadgetSpan, adjustedContactVertex, contactPoint]
  · rw [contactGadgetRightNode, dite_eq_right hk]
    change contactPoint (contactGadgetRightOrigin negative central) 0 +
      adjustedContactVertex rightLengths rightHeight (k.val - 1 + 1) = _
    congr 2
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    omega

/-- Every physical link has its independently prescribed length. -/
theorem contactGadget_link_lengths (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central)
    (leftLengths rightLengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths k)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths k)
    {leftHeight rightHeight : ℝ}
    (hleftHeight : leftHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hrightHeight : rightHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hleft : adjustedContactSpan leftLengths leftHeight = contactGadgetSpan negative central) :
    (∀ k : Fin 9,
      dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (Sum.inl k.succ))
        (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (Sum.inl k.castSucc)) = leftLengths k.val) ∧
    dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        contactGadgetSide)
      (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (Sum.inl 9)) = central ∧
    (∀ k : Fin 9,
      dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (contactGadgetRightNode negative k.succ))
        (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (contactGadgetRightNode negative k.castSucc)) = rightLengths k.val) := by
  have hs := contactGadgetSlope_bounds negative
  have hcentral : 0 ≤ central := by unfold contactLengthTolerance at hc; linarith
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact adjustedContact_link_length hs.1 hs.2 hleftHeight leftLengths hl k.isLt
  · have hA : contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (Sum.inl 9) = contactPoint (contactGadgetSpan negative central) 0 := by
      change adjustedContactVertex leftLengths leftHeight 9 = _
      rw [adjustedContactVertex_end, hleft]
    rw [hA]
    have hsq : dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        contactGadgetSide) (contactPoint (contactGadgetSpan negative central) 0) ^ 2 = central ^ 2 := by
      cases negative <;> simp only [contactGadgetSide, contactGadgetPosition, Sum.elim_inr,
        contactGadgetRightOrigin, contactGadgetSpan, Bool.false_eq_true, ite_false,
        ite_true, contactPoint_dist_sq] <;> ring
    nlinarith [show 0 ≤ dist (contactGadgetPosition negative central leftLengths rightLengths
      leftHeight rightHeight contactGadgetSide) (contactPoint (contactGadgetSpan negative central) 0)
      from dist_nonneg]
  · intro k
    rw [contactGadgetRightNode_position negative central leftLengths rightLengths leftHeight rightHeight hleft,
      contactGadgetRightNode_position negative central leftLengths rightLengths leftHeight rightHeight hleft,
      dist_add_left]
    exact adjustedContact_link_length hs.1 hs.2 hrightHeight rightLengths hr k.isLt

/-- Independent implementation of all nineteen links with the two original
vertices fixed. No dimensional parameter of a larger lattice enters. -/
theorem contactGadget_independent_lengths (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance)
    (leftLengths rightLengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths k)
    (hl' : ∀ k < 9, leftLengths k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths k)
    (hr' : ∀ k < 9, rightLengths k ≤ 1 + contactLengthTolerance) :
    ∃ leftHeight rightHeight,
      leftHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
        (contactHeightHigh (contactGadgetSlope negative)) ∧
      rightHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
        (contactHeightHigh (contactGadgetSlope negative)) ∧
      adjustedContactSpan leftLengths leftHeight = contactGadgetSpan negative central ∧
      adjustedContactSpan rightLengths rightHeight = contactGadgetSpan negative central ∧
      contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight (Sum.inl 0) =
        contactPoint 0 0 ∧
      contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (contactGadgetRightNode negative 9) = contactPoint 17 0 := by
  have hs := contactGadgetSlope_bounds negative
  have hspan := contactGadgetSpan_bounds negative hc hc'
  obtain ⟨leftHeight, hleftHeight, hleft⟩ := adjustedContactSpan_exists hs.1 hs.2 leftLengths hl hl' hspan.1 hspan.2
  obtain ⟨rightHeight, hrightHeight, hright⟩ := adjustedContactSpan_exists hs.1 hs.2 rightLengths hr hr' hspan.1 hspan.2
  refine ⟨leftHeight, rightHeight, hleftHeight, hrightHeight, hleft, hright, ?_, ?_⟩
  · simp [contactGadgetPosition, adjustedContactVertex]
  · rw [contactGadgetRightNode_position negative central leftLengths rightLengths leftHeight rightHeight hleft]
    change contactPoint (contactGadgetRightOrigin negative central) 0 +
      adjustedContactVertex rightLengths rightHeight 9 = contactPoint 17 0
    rw [adjustedContactVertex_end, hright]
    cases negative
    · ext i
      fin_cases i
      · change (17 + central) / 2 + (17 - central) / 2 = 17
        ring
      · norm_num [contactPoint, PiLp.add_apply]
    · ext i
      fin_cases i <;> norm_num [contactGadgetRightOrigin, contactGadgetSpan, contactPoint, PiLp.add_apply]

end ContinuumCoulomb

end

end OAI
