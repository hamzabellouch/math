import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactBaseSeparation

namespace OAI

/-! The actual gadget sites fit the common lattice strips. Together with
ContactStrips, this separates distinct edges without a size-dependent loss. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactPoint_eta (p : ContactPoint) : contactPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl

/-- Every base-gadget site other than the two original vertices belongs to
the uniform internal strip. -/
theorem contactBaseGadget_internal_strip (negative : Bool) (x : ContactGadgetSite)
    (hleft : x ≠ Sum.inl 0) (hright : x ≠ contactGadgetRightNode negative 9) :
    ∃ p : ContactStripSite,
      contactBaseGadgetPosition negative x = contactPoint p.axial p.transverse := by
  have hs := contactGadgetSlope_bounds negative
  rcases x with i | (i | ⟨⟩)
  · have hi : 1 ≤ i.val := by
      have hv : i.val ≠ 0 := fun h => hleft (congrArg Sum.inl (Fin.ext h))
      omega
    let p := leftContactStripSite (contactGadgetSlope negative) hs.1 hs.2 i.val hi
      (show i.val ≤ 9 by have := i.isLt; omega)
    exact ⟨p, (contactPoint_eta (contactPathVertex (contactGadgetSlope negative) i.val)).symm⟩
  · have hi8 : i.val ≠ 8 := by
      intro h
      have hi : i = 8 := Fin.ext h
      subst i
      apply hright
      norm_num [contactGadgetRightNode]
    have hi : i.val + 1 ≤ 8 := by have := i.isLt; omega
    have horigin : contactGadgetRightOrigin negative 1 + (5 + 4 * contactGadgetSlope negative) = 17 := by
      cases negative <;> norm_num [contactGadgetRightOrigin, contactGadgetSlope]
    let p := rightContactStripSite (contactGadgetSlope negative) (contactGadgetRightOrigin negative 1)
      hs.1 hs.2 horigin (i.val + 1) (by omega) hi
    refine ⟨p, ?_⟩
    change contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (i.val + 1) =
      contactPoint (contactGadgetRightOrigin negative 1 +
        contactPathVertex (contactGadgetSlope negative) (i.val + 1) 0)
        (contactPathVertex (contactGadgetSlope negative) (i.val + 1) 1)
    ext j
    fin_cases j <;> simp [contactPoint, PiLp.add_apply]
  · cases negative
    · let p : ContactStripSite := {
        axial := 9
        transverse := 0
        axial_lower := by norm_num
        axial_upper := by norm_num
        transverse_lower := by norm_num
        transverse_upper := by norm_num
        off_axis_lower := by intro h; exact False.elim (h rfl)
        off_axis_upper := by intro h; exact False.elim (h rfl) }
      exact ⟨p, rfl⟩
    · let p : ContactStripSite := {
        axial := 17 / 2
        transverse := 1
        axial_lower := by norm_num
        axial_upper := by norm_num
        transverse_lower := by norm_num
        transverse_upper := by norm_num
        off_axis_lower := by intro _; norm_num
        off_axis_upper := by intro _; norm_num }
      exact ⟨p, rfl⟩

/-- Perpendicular-edge separation persists for the actual adjusted nodes. -/
theorem perpendicularContact_perturbed_separation (a b c d : ℤ) (p q : ContactStripSite)
    (x y : ContactPoint) (hx : dist (horizontalContact a b p) x ≤ 1 / 20)
    (hy : dist (verticalContact c d q) y ≤ 1 / 20) : 6 / 5 < dist x y :=
  contact_separation_stable _ _ _ _ (perpendicularContact_separation a b c d p q).le hx hy

/-- Parallel-edge separation persists with the same fixed margin. -/
theorem horizontalContact_perturbed_separation (a b c d : ℤ)
    (hne : (a, b) ≠ (c, d)) (p q : ContactStripSite)
    (x y : ContactPoint) (hx : dist (horizontalContact a b p) x ≤ 1 / 20)
    (hy : dist (horizontalContact c d q) y ≤ 1 / 20) : 6 / 5 < dist x y :=
  contact_separation_stable _ _ _ _ (horizontalContact_separation a b c d hne p q).le hx hy

end ContinuumCoulomb

end

end OAI
