import OAI.Probability.SLE.Geometry.DiskBoundaryRegion
import OAI.Probability.SLE.Geometry.ClosedComplexPair

namespace OAI

/-! Assemble two compatible side maps into a homeomorphism of the closed disk. -/
noncomputable section
open Set Complex Metric
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge

lemma closedLowerDisk_isClosed : IsClosed closedLowerDisk :=
  (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le Complex.continuous_im continuous_const)

def closedDiskTwoSideHomeomorph {A B : Set ℂ}
    (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ∪ B=closedBall (0:ℂ) 1)
    (H G : ℂ ≃ₜ ℂ)
    (hH : H '' A=closedUpperDisk) (hG : G '' B=closedLowerDisk)
    (he : ∀ z ∈ A ∩ B, H z=G z)
    (hi : ∀ z ∈ closedUpperDisk ∩ closedLowerDisk, H.symm z=G.symm z) :
    closedBall (0:ℂ) 1 ≃ₜ closedBall (0:ℂ) 1 := by
  let e : A ≃ₜ closedUpperDisk := (H.image A).trans (Homeomorph.setCongr hH)
  let d : B ≃ₜ closedLowerDisk := (G.image B).trans (Homeomorph.setCongr hG)
  let F := closedComplexPairHomeomorph hA closedUpperDisk_isClosed hB
    closedLowerDisk_isClosed e d (fun x hx => he x ⟨x.property,hx⟩)
    (fun x hx => hi x ⟨x.property,hx⟩)
  exact ((Homeomorph.setCongr hAB.symm).trans F).trans
    (Homeomorph.setCongr closed_halfDisks_union)

lemma closedDiskTwoSideHomeomorph_apply {A B : Set ℂ}
    (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ∪ B=closedBall (0:ℂ) 1)
    (H G : ℂ ≃ₜ ℂ)
    (hH : H '' A=closedUpperDisk) (hG : G '' B=closedLowerDisk)
    (he : ∀ z ∈ A ∩ B, H z=G z)
    (hi : ∀ z ∈ closedUpperDisk ∩ closedLowerDisk, H.symm z=G.symm z)
    (z : closedBall (0:ℂ) 1) :
    (closedDiskTwoSideHomeomorph hA hB hAB H G hH hG he hi z : ℂ)=
      if z.val ∈ A then H z else G z := by
  classical
  change (if ha : z.val ∈ A then H z else
    if hb : z.val ∈ B then G z else z.val)=_
  by_cases ha : z.val ∈ A
  · rw [dite_eq_left ha,ite_eq_left ha]
  · have hb : z.val ∈ B := ((hAB.symm ▸ z.property) : z.val ∈ A ∪ B).resolve_left ha
    rw [dite_eq_right ha,dite_eq_left hb,ite_eq_right ha]

end SLEExactGauge

end

end OAI
