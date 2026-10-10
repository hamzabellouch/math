import OAI.Analysis.SphereIsometry.AlignmentSet
import OAI.Analysis.SphereIsometry.ReturnMapEstimate
import OAI.Analysis.SphereIsometry.ReturnMapFixedPoint
import OAI.Analysis.SphereIsometry.AlignedConfiguration

namespace OAI

/-!
# Alignment from an attained positive defect

The actual positive schedule supplies the invariant convex set; the actual
return-map estimate and the proved fixed-point theorem supply its fixed point.
The original center and scalar remain unchanged throughout the construction.
-/

noncomputable section

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A fixed point of the genuine sphere return map gives the exact four chords. -/
def aligned_of_return_fixed
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1) (hb : HasDefectBound f M)
    (v : UnitSphere X) (hv : v ∈ extremalSphere f y t ht M)
    (hfixed : returnSphere f y t ht v = v) : AlignedConfiguration f y t M where
  x := xPoint f y t ht v
  z := zPoint f y t ht v
  v := v
  w := wDirection f y t ht v
  p := pRadius f y t ht v
  r := rRadius f y t ht v
  s := sRadius f y t ht v
  u := uRadius f y t ht v
  p_pos := pRadius_pos f y t ht v
  r_pos := rRadius_pos f y t ht v
  s_pos := sRadius_pos f y t ht v
  u_pos := uRadius_pos f y t ht v
  x_eq := xPoint_eq f y t ht v
  z_eq := by simpa only [hfixed] using zPoint_eq f y t ht v
  fx_eq := fxPoint_eq f y t ht v
  fz_eq := fzPoint_eq f y t ht v
  s_sub_p := hv
  r_sub_u := (extremal_radius_identities f y t ht M hb hv).1
  chord_sum := (extremal_radius_identities f y t ht M hb hv).2.1
  chord_le_two := by
    calc
      pRadius f y t ht v + rRadius f y t ht v =
          ‖pRadius f y t ht v • (v : X) +
            rRadius f y t ht v • (returnSphere f y t ht v : X)‖ :=
        (extremal_radius_identities f y t ht M hb hv).2.2.symm
      _ = ‖(xPoint f y t ht v : X) - (zPoint f y t ht v : X)‖ :=
        (norm_xPoint_sub_zPoint f y t ht v).symm
      _ ≤ ‖(xPoint f y t ht v : X)‖ + ‖(zPoint f y t ht v : X)‖ := norm_sub_le _ _
      _ = 2 := by rw [UnitSphere.norm_coe, UnitSphere.norm_coe]; norm_num

/-- Alignment has no supplied invariant-set, contraction or fixed-point premise. -/
theorem exists_alignedConfiguration [CompleteSpace X]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y x₀ : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1) (hM : 0 < M)
    (hb : HasDefectBound f M) (hatt : signedDefect f t x₀ y = M) :
    Nonempty (AlignedConfiguration f y t M) := by
  obtain ⟨C, hCne, hCclosed, hCb, hCconvex, hCE, hg, hgC⟩ :=
    exists_return_invariant_convex f y x₀ t M ht hb hatt
  have hbounds : ∀ v ∈ C,
      (1 - t ≤ pAmbient f y t ht v ∧ pAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ sAmbient f y t ht v ∧ sAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ uAmbient f y t ht v ∧ uAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ rAmbient f y t ht v ∧ rAmbient f y t ht v ≤ 1 + t) := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := hCE hv
    simpa only [pAmbient_coe, sAmbient_coe, uAmbient_coe, rAmbient_coe, Set.mem_Icc] using
      radii_bounds f y t ht a
  have hs : ∀ v ∈ C, sAmbient f y t ht v = pAmbient f y t ht v + M := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hCE hv
    simpa only [sAmbient_coe, pAmbient_coe] using sRadius_eq_add f y t ht M ha
  have hr : ∀ v ∈ C, rAmbient f y t ht v = uAmbient f y t ht v + M := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hCE hv
    simpa only [rAmbient_coe, uAmbient_coe] using rRadius_eq_add f y t ht M hb ha
  have hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (returnAmbient f y t ht v) (returnAmbient f y t ht v') ≤
        (uAmbient f y t ht v * pAmbient f y t ht v /
          (rAmbient f y t ht v * sAmbient f y t ht v)) * dist v v' +
        2 * |uAmbient f y t ht v - uAmbient f y t ht v'| / rAmbient f y t ht v +
        2 * uAmbient f y t ht v * |pAmbient f y t ht v - pAmbient f y t ht v'| /
          (rAmbient f y t ht v * sAmbient f y t ht v) := by
    intro v hv v' hv'
    simpa only [dist_eq_norm] using
      returnAmbient_pair_estimate_on f y t ht M hb C hCE hv hv'
  obtain ⟨v, hv, hfixed⟩ := exists_fixedPoint_of_return_estimate
    ht.1 ht.2 hM hCne hCclosed hCb hCconvex hg hgC hbounds hs hr hpair
  obtain ⟨a, ha, rfl⟩ := hCE hv
  have hfixedSphere : returnSphere f y t ht a = a := by
    apply Subtype.ext
    simpa only [returnAmbient_coe] using hfixed
  exact ⟨aligned_of_return_fixed f y t M ht hb a ha hfixedSphere⟩

end Tingley

end

end OAI
