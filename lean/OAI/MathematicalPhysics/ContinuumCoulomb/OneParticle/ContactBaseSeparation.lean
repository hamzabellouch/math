import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactGadgets
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactPathBounds
import Mathlib.Data.Nat.Dist

namespace OAI

/-! The exact nineteen-link base gadget and all of its nonlink separations. -/

noncomputable section
namespace ContinuumCoulomb

def contactBaseGadgetPosition (negative : Bool) : ContactGadgetSite → ContactPoint :=
  Sum.elim (fun k => contactPathVertex (contactGadgetSlope negative) k.val)
    (Sum.elim (fun k => contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (k.val + 1))
      (fun _ => if negative then contactPoint (17 / 2) 1 else contactPoint 9 0))

def contactGadgetLinked (negative : Bool) : ContactGadgetSite → ContactGadgetSite → Prop
  | Sum.inl i, Sum.inl j => Nat.dist i.val j.val = 1
  | Sum.inl i, Sum.inr (Sum.inl j) => negative = true ∧ i = 9 ∧ j = 0
  | Sum.inr (Sum.inl j), Sum.inl i => negative = true ∧ i = 9 ∧ j = 0
  | Sum.inl i, Sum.inr (Sum.inr _) => i = 9
  | Sum.inr (Sum.inr _), Sum.inl i => i = 9
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => Nat.dist i.val j.val = 1
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr _) => negative = false ∧ i = 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl i) => negative = false ∧ i = 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => False

theorem contactPath_second_axial_lower {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : 2 ≤ k) : 2 ≤ contactPathVertex c k 0 := by
  have h := contactPath_horizontal_lower (by linarith : c ≤ 1) hk
  have h2 : contactPathVertex c 2 0 = 2 := by
    norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ, contactStepX]
  rw [h2] at h
  have hn : 0 ≤ c * (k - 2 : ℕ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  linarith

theorem contact_axial_separation (p q : ContactPoint) {margin : ℝ}
    (h : margin ≤ p 0 - q 0) : margin ≤ dist p q :=
  h.trans ((le_abs_self _).trans (contactPoint_coordinate_le_dist p q 0))

theorem contactBase_left_left_separation (negative : Bool) (i j : Fin 10)
    (hne : i ≠ j) (hlink : Nat.dist i.val j.val ≠ 1) :
    7 / 5 ≤ dist (contactPathVertex (contactGadgetSlope negative) i.val)
      (contactPathVertex (contactGadgetSlope negative) j.val) := by
  have hs := contactGadgetSlope_bounds negative
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt h)] at hlink
    rw [dist_comm]
    exact (by norm_num : (7 / 5 : ℝ) ≤ 3 / 2).trans
      (contactPath_nonlink_separation hs.1 (by linarith [hs.2]) (by omega))
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_lt h)] at hlink
    exact (by norm_num : (7 / 5 : ℝ) ≤ 3 / 2).trans
      (contactPath_nonlink_separation hs.1 (by linarith [hs.2]) (by omega))

theorem contactBase_left_right_separation (negative : Bool) (i : Fin 10) (j : Fin 9)
    (hlink : ¬(negative = true ∧ i = 9 ∧ j = 0)) :
    7 / 5 ≤ dist (contactBaseGadgetPosition negative (Sum.inl i))
      (contactBaseGadgetPosition negative (Sum.inr (Sum.inl j))) := by
  have hs := contactGadgetSlope_bounds negative
  have hr := (leftContactStripSite (contactGadgetSlope negative) hs.1 hs.2
    (j.val + 1) (by omega) (by have := j.isLt; omega)).axial_lower
  change 1 ≤ contactPathVertex (contactGadgetSlope negative) (j.val + 1) 0 at hr
  have hl := (contactPath_axial_bounds hs.1 hs.2 (show i.val ≤ 9 by have := i.isLt; omega)).2
  rw [dist_comm]
  apply contact_axial_separation
  change 7 / 5 ≤ contactGadgetRightOrigin negative 1 +
    contactPathVertex (contactGadgetSlope negative) (j.val + 1) 0 -
      contactPathVertex (contactGadgetSlope negative) i.val 0
  cases negative
  · norm_num [contactGadgetRightOrigin, contactGadgetSlope] at *
    linarith
  · by_cases hi : i = 9
    · have hj : j ≠ 0 := fun hj => hlink ⟨rfl, hi, hj⟩
      have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hsecond := contactPath_second_axial_lower hs.1 hs.2 (show 2 ≤ j.val + 1 by omega)
      subst i
      change 7 / 5 ≤ 17 / 2 + contactPathVertex (7 / 8) (j.val + 1) 0 - contactPathVertex (7 / 8) 9 0
      rw [contactPathVertex_end, contactPoint_zero]
      norm_num [contactGadgetSlope] at hsecond ⊢
      linarith
    · have hi8 : i.val ≤ 8 := by
        have hv : i.val ≠ 9 := fun h => hi (Fin.ext h)
        have := i.isLt
        omega
      by_cases hi0 : i.val = 0
      · have hx : contactPathVertex (7 / 8) i.val 0 = 0 := by rw [hi0]; simp [contactPathVertex]
        norm_num [contactGadgetRightOrigin, contactGadgetSlope] at hr ⊢
        rw [hx]
        linarith
      · have hlast := (contactPath_internal_axial_bounds hs.1 hs.2 (show 1 ≤ i.val by omega) hi8).2
        norm_num [contactGadgetRightOrigin, contactGadgetSlope] at hr hlast ⊢
        linarith

theorem contactBase_side_left_separation (negative : Bool) (i : Fin 10) (hi : i ≠ 9) :
    7 / 5 ≤ dist (contactBaseGadgetPosition negative contactGadgetSide)
      (contactBaseGadgetPosition negative (Sum.inl i)) := by
  have hs := contactGadgetSlope_bounds negative
  have hi8 : i.val ≤ 8 := by
    have hv : i.val ≠ 9 := fun h => hi (Fin.ext h)
    have := i.isLt
    omega
  cases negative
  · apply contact_axial_separation
    change 7 / 5 ≤ 9 - contactPathVertex (3 / 4) i.val 0
    by_cases hi0 : i.val = 0
    · rw [hi0]
      norm_num [contactPathVertex]
    · have hlast := (contactPath_internal_axial_bounds hs.1 hs.2 (show 1 ≤ i.val by omega) hi8).2
      norm_num [contactGadgetSlope] at hlast
      linarith
  · by_cases hi' : i.val = 8
    · have hx : contactPathVertex (7 / 8) i.val = contactPoint (15 / 2) 0 := by
        rw [hi']
        ext k
        fin_cases k <;> norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ,
          contactStepX, contactStepY]
      change 7 / 5 ≤ dist (contactPoint (17 / 2) 1) (contactPathVertex (7 / 8) i.val)
      rw [hx]
      have hd := contactPoint_dist_sq (17 / 2) 1 (15 / 2) 0
      norm_num at hd
      nlinarith [show 0 ≤ dist (contactPoint (17 / 2) 1) (contactPoint (15 / 2) 0) from dist_nonneg]
    · have hproj := contactPath_horizontal_lower (c := (7 / 8 : ℝ)) (by norm_num)
        (show i.val ≤ 9 by omega)
      rw [contactPathVertex_end, contactPoint_zero] at hproj
      have hcount : (2 : ℝ) ≤ (9 - i.val : ℕ) := by exact_mod_cast (show 2 ≤ 9 - i.val by omega)
      apply contact_axial_separation
      change 7 / 5 ≤ 17 / 2 - contactPathVertex (7 / 8) i.val 0
      norm_num at hproj
      nlinarith

theorem contactBase_side_right_separation (negative : Bool) (j : Fin 9)
    (hlink : ¬(negative = false ∧ j = 0)) :
    7 / 5 ≤ dist (contactBaseGadgetPosition negative contactGadgetSide)
      (contactBaseGadgetPosition negative (Sum.inr (Sum.inl j))) := by
  have hs := contactGadgetSlope_bounds negative
  cases negative
  · have hj : j ≠ 0 := fun h => hlink ⟨rfl, h⟩
    have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hsecond := contactPath_second_axial_lower hs.1 hs.2 (show 2 ≤ j.val + 1 by omega)
    rw [dist_comm]
    apply contact_axial_separation
    change 7 / 5 ≤ (contactGadgetRightOrigin false 1 + contactPathVertex (3 / 4) (j.val + 1) 0) - 9
    norm_num [contactGadgetRightOrigin, contactGadgetSlope] at hsecond ⊢
    linarith
  · by_cases hj : j = 0
    · subst j
      have hx : contactPoint (17 / 2) 0 + contactPathVertex (7 / 8) 1 = contactPoint (19 / 2) 0 := by
        ext k
        fin_cases k <;> norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ,
          contactStepX, contactStepY, PiLp.add_apply]
      change 7 / 5 ≤ dist (contactPoint (17 / 2) 1)
        (contactPoint (17 / 2) 0 + contactPathVertex (7 / 8) 1)
      rw [hx]
      have hd := contactPoint_dist_sq (17 / 2) 1 (19 / 2) 0
      norm_num at hd
      nlinarith [show 0 ≤ dist (contactPoint (17 / 2) 1) (contactPoint (19 / 2) 0) from dist_nonneg]
    · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hsecond := contactPath_second_axial_lower hs.1 hs.2 (show 2 ≤ j.val + 1 by omega)
      rw [dist_comm]
      apply contact_axial_separation
      change 7 / 5 ≤ (contactGadgetRightOrigin true 1 + contactPathVertex (7 / 8) (j.val + 1) 0) - 17 / 2
      norm_num [contactGadgetRightOrigin, contactGadgetSlope] at hsecond ⊢
      linarith

/-- Every distinct nonlinked pair in either actual base gadget is at
least1.4 apart, including the negative-sign side site. -/
theorem contactBaseGadget_nonlink_separation (negative : Bool) (x y : ContactGadgetSite)
    (hne : x ≠ y) (hlink : ¬ contactGadgetLinked negative x y) :
    7 / 5 ≤ dist (contactBaseGadgetPosition negative x) (contactBaseGadgetPosition negative y) := by
  rcases x with i | (i | ⟨⟩) <;> rcases y with j | (j | ⟨⟩)
  · exact contactBase_left_left_separation negative i j (fun h => hne (congrArg Sum.inl h)) hlink
  · exact contactBase_left_right_separation negative i j hlink
  · rw [dist_comm]
    exact contactBase_side_left_separation negative i hlink
  · rw [dist_comm]
    exact contactBase_left_right_separation negative j i hlink
  · change 7 / 5 ≤ dist (contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (i.val + 1))
      (contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (j.val + 1))
    rw [dist_add_left]
    have hi10 : i.val + 1 < 10 := by have := i.isLt; omega
    have hj10 : j.val + 1 < 10 := by have := j.isLt; omega
    apply contactBase_left_left_separation negative ⟨i.val + 1, hi10⟩ ⟨j.val + 1, hj10⟩
    · intro h
      have hv := congrArg Fin.val h
      have hij : i = j := Fin.ext (by simpa using hv)
      exact hne (congrArg (fun k : Fin 9 => (Sum.inr (Sum.inl k) : ContactGadgetSite)) hij)
    · change Nat.dist (i.val + 1) (j.val + 1) ≠ 1
      simpa only [Nat.dist_add_add_right, contactGadgetLinked] using hlink
  · rw [dist_comm]
    exact contactBase_side_right_separation negative i hlink
  · exact contactBase_side_left_separation negative j hlink
  · exact contactBase_side_right_separation negative j hlink
  · exact False.elim (hne rfl)

end ContinuumCoulomb

end

end OAI
