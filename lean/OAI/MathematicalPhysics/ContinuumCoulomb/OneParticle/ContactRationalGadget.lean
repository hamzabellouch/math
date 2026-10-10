import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactClosedCoordinates
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactGadgetStability

namespace OAI

/-! A concrete rational twenty-site gadget. The two paths share the same
rational prescribed span; their outer endpoints are exact and their
internal vertices approximate the original independent-length gadget. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalGadget
open ContactHeightEvaluation

abbrev Input := ℕ × (Bool × (ℚ × (List ℚ × List ℚ)))

def span (negative : Bool) (central : ℚ) : ℚ :=
  if negative then 17 / 2 else (17 - central) / 2

def origin (negative : Bool) (central : ℚ) : ℚ :=
  if negative then 17 / 2 else (17 + central) / 2

def leftEnvironment (x : Input) : Environment :=
  (x.1, (x.2.2.2.1, span x.2.1 x.2.2.1))

def rightEnvironment (x : Input) : Environment :=
  (x.1, (x.2.2.2.2, span x.2.1 x.2.2.1))

def position (x : Input) : ContactGadgetSite → ℚ × ℚ :=
  Sum.elim (fun k => closedVertex (leftEnvironment x) k.val)
    (Sum.elim (fun k =>
      (origin x.2.1 x.2.2.1 + (closedVertex (rightEnvironment x) (k.val + 1)).1,
        (closedVertex (rightEnvironment x) (k.val + 1)).2))
      (fun _ => if x.2.1 then (17 / 2, x.2.2.1) else (origin x.2.1 x.2.2.1, 0)))

def point (x : Input) (s : ContactGadgetSite) : ContactPoint :=
  contactPoint (position x s).1 (position x s).2

def leftLengths (x : Input) (k : ℕ) : ℝ := lengthAt (leftEnvironment x) k
def rightLengths (x : Input) (k : ℕ) : ℝ := lengthAt (rightEnvironment x) k

theorem span_cast (b : Bool) (c : ℚ) :
    (span b c : ℝ) = contactGadgetSpan b c := by
  cases b <;> simp [span, contactGadgetSpan, Rat.cast_div, Rat.cast_sub]

theorem origin_cast (b : Bool) (c : ℚ) :
    (origin b c : ℝ) = contactGadgetRightOrigin b c := by
  cases b <;> simp [origin, contactGadgetRightOrigin, Rat.cast_div, Rat.cast_add]

theorem point_left (x : Input) (k : Fin 10) :
    point x (Sum.inl k) = closedVertexPoint (leftEnvironment x) k.val := rfl

theorem point_right (x : Input) (k : Fin 9) :
    point x (Sum.inr (Sum.inl k)) =
      contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 +
        closedVertexPoint (rightEnvironment x) (k.val + 1) := by
  ext i
  fin_cases i <;>
    simp [point, position, closedVertexPoint, contactPoint, Rat.cast_add,
      origin_cast, PiLp.add_apply]

theorem point_side (x : Input) :
    point x contactGadgetSide =
      if x.2.1 then contactPoint (17 / 2) x.2.2.1
      else contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 := by
  cases hb : x.2.1 <;>
    simp [point, position, contactGadgetSide, hb, origin_cast, Rat.cast_div]

theorem point_start (x : Input) : point x (Sum.inl 0) = contactPoint 0 0 := by
  rw [point_left]
  simp [closedVertexPoint, closedVertex_start]

theorem point_end (x : Input) :
    point x (contactGadgetRightNode x.2.1 9) = contactPoint 17 0 := by
  have hnode : contactGadgetRightNode x.2.1 9 = Sum.inr (Sum.inl 8) := by
    simp [contactGadgetRightNode]
  rw [hnode, point_right]
  change contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 +
    closedVertexPoint (rightEnvironment x) 9 = _
  simp only [closedVertexPoint, closedVertex_end, rightEnvironment, span_cast, Rat.cast_zero]
  cases hb : x.2.1 <;> ext i <;> fin_cases i
  all_goals simp [contactGadgetRightOrigin, contactGadgetSpan, contactPoint, PiLp.add_apply]
  all_goals ring

theorem point_near_reference (x : Input) (hL hR : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths x k)
    (hl' : ∀ k < 9, leftLengths x k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths x k)
    (hr' : ∀ k < 9, rightLengths x k ≤ 1 + contactLengthTolerance)
    (hLmem : hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
      (contactHeightHigh (contactGadgetSlope x.2.1)))
    (hRmem : hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
      (contactHeightHigh (contactGadgetSlope x.2.1)))
    (hLroot : adjustedContactSpan (leftLengths x) hL = contactGadgetSpan x.2.1 x.2.2.1)
    (hRroot : adjustedContactSpan (rightLengths x) hR = contactGadgetSpan x.2.1 x.2.2.1)
    (s : ContactGadgetSite) :
    dist (point x s)
      (contactGadgetPosition x.2.1 x.2.2.1 (leftLengths x) (rightLengths x) hL hR s) ≤
        36 * ((x.1 : ℝ) + 1)⁻¹ := by
  have hs := contactGadgetSlope_bounds x.2.1
  have hL' := contactHeight_interval_bounds hs.1 hs.2 hLmem
  have hR' := contactHeight_interval_bounds hs.1 hs.2 hRmem
  have hLroot' : adjustedContactSpan (leftLengths x) hL =
      ((leftEnvironment x).2.2 : ℝ) := by simpa only [leftEnvironment, span_cast] using hLroot
  have hRroot' : adjustedContactSpan (rightLengths x) hR =
      ((rightEnvironment x).2.2 : ℝ) := by simpa only [rightEnvironment, span_cast] using hRroot
  rcases s with k | (k | u)
  · rw [point_left]
    exact closedVertex_error (leftEnvironment x) hL hl hl' hL' hLroot'
      (by have := k.isLt; omega)
  · rw [point_right]
    change dist (_ + _) (_ + _) ≤ _
    rw [dist_add_left]
    exact closedVertex_error (rightEnvironment x) hR hr hr' hR' hRroot'
      (by have := k.isLt; omega)
  · cases u
    change dist (point x contactGadgetSide) _ ≤ _
    rw [point_side]
    change dist _ (if x.2.1 then _ else _) ≤ _
    rw [dist_self]
    positivity

theorem exists_reference (x : Input)
    (hc : 1 - contactLengthTolerance ≤ (x.2.2.1 : ℝ))
    (hc' : (x.2.2.1 : ℝ) ≤ 1 + contactLengthTolerance)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths x k)
    (hl' : ∀ k < 9, leftLengths x k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths x k)
    (hr' : ∀ k < 9, rightLengths x k ≤ 1 + contactLengthTolerance) :
    ∃ hL hR,
      hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
        (contactHeightHigh (contactGadgetSlope x.2.1)) ∧
      hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
        (contactHeightHigh (contactGadgetSlope x.2.1)) ∧
      adjustedContactSpan (leftLengths x) hL = contactGadgetSpan x.2.1 x.2.2.1 ∧
      adjustedContactSpan (rightLengths x) hR = contactGadgetSpan x.2.1 x.2.2.1 ∧
      ∀ s, dist (point x s)
        (contactGadgetPosition x.2.1 x.2.2.1 (leftLengths x) (rightLengths x) hL hR s) ≤
          36 * ((x.1 : ℝ) + 1)⁻¹ := by
  have hs := contactGadgetSlope_bounds x.2.1
  have hspan := contactGadgetSpan_bounds x.2.1 hc hc'
  obtain ⟨hL, hLmem, hLroot⟩ := adjustedContactSpan_exists hs.1 hs.2
    (leftLengths x) hl hl' hspan.1 hspan.2
  obtain ⟨hR, hRmem, hRroot⟩ := adjustedContactSpan_exists hs.1 hs.2
    (rightLengths x) hr hr' hspan.1 hspan.2
  exact ⟨hL, hR, hLmem, hRmem, hLroot, hRroot,
    point_near_reference x hL hR hl hl' hr hr' hLmem hRmem hLroot hRroot⟩

theorem reference_near_base (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance)
    (ll rr : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ ll k)
    (hl' : ∀ k < 9, ll k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rr k)
    (hr' : ∀ k < 9, rr k ≤ 1 + contactLengthTolerance)
    {hL hR : ℝ}
    (hLmem : hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hRmem : hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative))) (s : ContactGadgetSite) :
    dist (contactGadgetPosition negative central ll rr hL hR s)
      (contactBaseGadgetPosition negative s) < 9 / 200 := by
  have hs := contactGadgetSlope_bounds negative
  rcases s with k | (k | ⟨⟩)
  · exact (adjustedContactVertex_displacement hs.1 hs.2 hLmem ll hl hl'
      (by have := k.isLt; omega)).trans (by norm_num)
  · have hp := adjustedContactVertex_displacement hs.1 hs.2 hRmem rr hr hr'
      (show k.val + 1 ≤ 9 by have := k.isLt; omega)
    have ho := contactGadgetOrigin_near negative hc hc'
    have hd := dist_add_add_le (contactPoint (contactGadgetRightOrigin negative central) 0)
      (adjustedContactVertex rr hR (k.val + 1))
      (contactPoint (contactGadgetRightOrigin negative 1) 0)
      (contactPathVertex (contactGadgetSlope negative) (k.val + 1))
    change dist (_ + _) (_ + _) < _
    unfold contactLengthTolerance at ho
    linarith
  · cases negative
    · have ho := contactGadgetOrigin_near false hc hc'
      norm_num [contactGadgetRightOrigin, contactLengthTolerance] at ho
      change dist (contactPoint ((17 + central) / 2) 0) (contactPoint 9 0) < _
      linarith
    · change dist (contactPoint (17 / 2) central) (contactPoint (17 / 2) 1) < _
      rw [contactPoint_vertical_dist]
      have habs : |central - 1| ≤ contactLengthTolerance := abs_le.mpr ⟨by linarith, by linarith⟩
      exact habs.trans_lt (by norm_num [contactLengthTolerance])

end ContinuumCoulomb.ContactRationalGadget

end

end OAI
