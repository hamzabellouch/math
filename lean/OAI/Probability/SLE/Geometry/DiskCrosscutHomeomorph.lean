import OAI.Probability.SLE.Geometry.DiskSideRegionImages
import OAI.Probability.SLE.Geometry.DiskTwoSideGlue

namespace OAI

/-! A parameter-preserving disk crosscut extension, fixing the whole circle. -/
noncomputable section
open Set Complex Metric

namespace SLEExactGauge

theorem disk_crosscut_homeomorph
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (h0 : p 0=-1) (h1 : p 1=1) (hp : ∀ s ∈ Ioo 0 1, ‖p s‖ < 1) :
    ∃ e : closedBall (0:ℂ) 1 ≃ₜ closedBall (0:ℂ) 1,
      (∀ s ∈ Icc 0 1, ∀ hs : p s ∈ closedBall (0:ℂ) 1,
        (e ⟨p s,hs⟩:ℂ)=diskDiameter s) ∧
      ∀ z : closedBall (0:ℂ) 1, ‖(z:ℂ)‖=1 → (e z:ℂ)=z := by
  classical
  let A := closure (complexInside (diskUpperArc '' Icc 0 1 ∪ p '' Icc 0 1))
  let B := closure (complexInside (diskLowerArc '' Icc 0 1 ∪ p '' Icc 0 1))
  obtain ⟨hAB,hmeet⟩ := disk_crosscut_closed_regions p hc hi h0 h1 hp
  change A ∪ B=closedBall (0:ℂ) 1 at hAB
  change A ∩ B=p '' Icc 0 1 at hmeet
  obtain ⟨H,hHP,hHA⟩ := disk_crosscut_upper_straightening p hc hi h0 h1 hp
  obtain ⟨G,hGP,hGB⟩ := disk_crosscut_lower_straightening p hc hi h0 h1 hp
  have hH := disk_upper_region_image p H hHP hHA
  have hG := disk_lower_region_image p G hGP hGB
  have he (z : ℂ) (hz : z ∈ A ∩ B) : H z=G z := by
    rw [hmeet] at hz
    obtain ⟨s,hs,rfl⟩ := hz
    rw [hHP s hs,hGP s hs]
  have hrev (z : ℂ) (hz : z ∈ closedUpperDisk ∩ closedLowerDisk) :
      H.symm z=G.symm z := by
    rw [closed_halfDisks_inter] at hz
    obtain ⟨s,hs,rfl⟩ := hz
    calc
      H.symm (diskDiameter s)=p s := by rw [← hHP s hs,H.symm_apply_apply]
      _=G.symm (diskDiameter s) := by rw [← hGP s hs,G.symm_apply_apply]
  let e := closedDiskTwoSideHomeomorph (show IsClosed A from isClosed_closure)
    (show IsClosed B from isClosed_closure) hAB H G hH hG he hrev
  have heval (z : closedBall (0:ℂ) 1) : (e z:ℂ)=if z.val ∈ A then H z else G z :=
    closedDiskTwoSideHomeomorph_apply _ _ hAB H G hH hG he hrev z
  have hPA (s : ℝ) (hs : s ∈ Icc 0 1) : p s ∈ A := by
    have hh : p s ∈ A ∩ B := by rw [hmeet]; exact ⟨s,hs,rfl⟩
    exact hh.1
  have hupper : Schoenflies.IsJordanCurve
      (complexPlaneCoordinates '' (diskUpperArc '' Icc 0 1 ∪ p '' Icc 0 1)) := by
    simpa only [union_comm] using disk_crosscut_upper_jordan p hc hi h0 h1 hp
  have hlower := disk_crosscut_lower_jordan p hc hi h0 h1 hp
  have hAc := complexInside_closure hupper
  have hBc := complexInside_closure hlower
  refine ⟨e,?_,?_⟩
  · intro s hs hps
    rw [heval,ite_eq_left (hPA s hs),hHP s hs]
  · intro z hz
    have hzAB : z.val ∈ diskUpperArc '' Icc 0 1 ∪ diskLowerArc '' Icc 0 1 := by
      rw [disk_semicircle_union]
      exact hz
    rcases hzAB with hzA|hzB
    · have hzAc : z.val ∈ A := by
        change z.val ∈ closure (complexInside _)
        rw [hAc]
        exact Or.inr (Or.inl hzA)
      rw [heval,ite_eq_left hzAc,hHA z hzA]
    · have hzBc : z.val ∈ B := by
        change z.val ∈ closure (complexInside _)
        rw [hBc]
        exact Or.inr (Or.inl hzB)
      rw [heval]
      split_ifs with hzAc
      · rw [he z ⟨hzAc,hzBc⟩,hGB z hzB]
      · exact hGB z hzB

end SLEExactGauge

end

end OAI
