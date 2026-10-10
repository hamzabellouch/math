import OAI.Probability.SLE.Geometry.DiskCrosscutClosedRegions

namespace OAI

/-! Each prescribed side extension transports the corresponding closed region. -/
noncomputable section
open Set Complex

namespace SLEExactGauge

lemma image_interval_of_agree (H : ℂ ≃ₜ ℂ) (p q : ℝ → ℂ)
    (h : ∀ s ∈ Icc 0 1, H (p s)=q s) : H '' (p '' Icc 0 1)=q '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨_,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨s,hs,(h s hs).symm⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨p s,mem_image_of_mem p hs,h s hs⟩

lemma image_eq_self_of_fixed (H : ℂ ≃ₜ ℂ) (A : Set ℂ)
    (h : ∀ z ∈ A, H z=z) : H '' A=A := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    rwa [h w hw]
  · intro hz
    exact ⟨z,hz,h z hz⟩

theorem disk_upper_region_image (p : ℝ → ℂ) (H : ℂ ≃ₜ ℂ)
    (hP : ∀ s ∈ Icc 0 1, H (p s)=diskDiameter s)
    (hA : ∀ z ∈ diskUpperArc '' Icc 0 1, H z=z) :
    H '' closure (complexInside (diskUpperArc '' Icc 0 1 ∪ p '' Icc 0 1))=
      closedUpperDisk := by
  rw [H.image_closure,complexInside_transport,image_union,
    image_interval_of_agree H p diskDiameter hP,
    image_eq_self_of_fixed H _ hA,union_comm,complexInside_upperDisk,openUpperDisk_closure]

theorem disk_lower_region_image (p : ℝ → ℂ) (H : ℂ ≃ₜ ℂ)
    (hP : ∀ s ∈ Icc 0 1, H (p s)=diskDiameter s)
    (hA : ∀ z ∈ diskLowerArc '' Icc 0 1, H z=z) :
    H '' closure (complexInside (diskLowerArc '' Icc 0 1 ∪ p '' Icc 0 1))=
      closedLowerDisk := by
  rw [H.image_closure,complexInside_transport,image_union,
    image_interval_of_agree H p diskDiameter hP,
    image_eq_self_of_fixed H _ hA,union_comm,complexInside_lowerDisk,openLowerDisk_closure]

end SLEExactGauge

end

end OAI
