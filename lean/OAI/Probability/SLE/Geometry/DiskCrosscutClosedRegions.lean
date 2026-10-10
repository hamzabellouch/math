import OAI.Probability.SLE.Geometry.DiskCrosscutPartition

namespace OAI

/-! The closures of the two disk crosscut regions cover the closed disk
and meet exactly along the crosscut. -/
noncomputable section
open Set Complex Metric
open scoped ComplexConjugate

namespace SLEExactGauge

theorem disk_crosscut_lower_jordan
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (h0 : p 0=-1) (h1 : p 1=1) (hp : ∀ s ∈ Ioo 0 1, ‖p s‖ < 1) :
    Schoenflies.IsJordanCurve
      (complexPlaneCoordinates '' (diskLowerArc '' Icc 0 1 ∪ p '' Icc 0 1)) := by
  have hpArc := complexPlaneCoordinates_isArcBetween p hc hi
  have haArc := complexPlaneCoordinates_isArcBetween diskLowerArc
    diskLowerArc_continuous.continuousOn diskLowerArc_injOn
  rw [diskLowerArc_zero,diskLowerArc_one,← h0,← h1] at haArc
  rw [image_union]
  apply Schoenflies.isJordanCurve_union haArc hpArc
  rintro _ ⟨_,⟨t,ht,rfl⟩,rfl⟩ ⟨_,⟨s,hs,rfl⟩,he⟩
  have heq : p s=diskLowerArc t := complexPlaneCoordinates.injective he
  have hend : s=0 ∨ s=1 := by
    by_contra hn
    have hs0 : 0<s := lt_of_le_of_ne hs.1 (by intro he; exact hn (Or.inl he.symm))
    have hs1 : s<1 := lt_of_le_of_ne hs.2 (by intro he; exact hn (Or.inr he))
    have hh := hp s ⟨hs0,hs1⟩
    rw [heq] at hh
    have hn1 : ‖diskLowerArc t‖=1 := by simpa [diskLowerArc] using diskUpperArc_norm t
    rw [hn1] at hh
    exact lt_irrefl _ hh
  rcases hend with rfl|rfl
  · exact Or.inl (by rw [← heq,h0,← diskLowerArc_zero])
  · exact Or.inr (by rw [← heq,h1,← diskLowerArc_one])

lemma complexInside_not_mem {C : Set ℂ} {z : ℂ} (hz : z ∈ complexInside C) : z ∉ C := by
  intro hc
  exact hz.1 (mem_image_of_mem complexPlaneCoordinates hc)

theorem disk_crosscut_closed_regions
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (h0 : p 0=-1) (h1 : p 1=1) (hp : ∀ s ∈ Ioo 0 1, ‖p s‖ < 1) :
    let U := complexInside (diskUpperArc '' Icc 0 1 ∪ p '' Icc 0 1)
    let V := complexInside (diskLowerArc '' Icc 0 1 ∪ p '' Icc 0 1)
    closure U ∪ closure V=closedBall (0:ℂ) 1 ∧
      closure U ∩ closure V=p '' Icc 0 1 := by
  dsimp only
  let A := diskUpperArc '' Icc 0 1
  let B := diskLowerArc '' Icc 0 1
  let P := p '' Icc 0 1
  let U := complexInside (A ∪ P)
  let V := complexInside (B ∪ P)
  have hJ : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' (A ∪ P)) := by
    simpa only [union_comm] using disk_crosscut_upper_jordan p hc hi h0 h1 hp
  have hL := disk_crosscut_lower_jordan p hc hi h0 h1 hp
  have hUc : closure U=U ∪ (A ∪ P) := complexInside_closure hJ
  have hVc : closure V=V ∪ (B ∪ P) := complexInside_closure hL
  obtain ⟨hpart,hdisj⟩ := disk_crosscut_partition p hc hi h0 h1 hp
  change ball (0:ℂ) 1 \ P=U ∪ V at hpart
  change Disjoint U V at hdisj
  have hUV : U ∪ V ⊆ ball (0:ℂ) 1 := by rw [← hpart]; exact sdiff_subset
  have hP : P ⊆ closedBall (0:ℂ) 1 := by
    rintro z ⟨s,hs,rfl⟩
    by_cases hs0 : s=0
    · simp [hs0,h0]
    by_cases hs1 : s=1
    · simp [hs1,h1]
    apply ball_subset_closedBall
    simpa only [mem_ball,dist_zero_right] using hp s
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),lt_of_le_of_ne hs.2 hs1⟩
  have hAB : A ∪ B={z : ℂ | ‖z‖=1} := disk_semicircle_union
  have hABn (z : ℂ) (hz : z ∈ A ∪ B) : z ∉ ball (0:ℂ) 1 := by
    rw [hAB] at hz
    change ‖z‖=1 at hz
    simpa only [mem_ball,dist_zero_right,hz,lt_self_iff_false] using not_false
  have hABP : A ∩ B ⊆ P := by
    rw [disk_semicircle_inter]
    intro z hz
    rcases hz with hz|hz
    · exact ⟨0,by norm_num,by simpa only [h0] using hz.symm⟩
    · exact ⟨1,by norm_num,by simpa only [h1] using hz.symm⟩
  rw [hUc,hVc]
  constructor
  · ext z
    constructor
    · rintro ((hz|hz)|(hz|hz))
      · exact ball_subset_closedBall (hUV (Or.inl hz))
      · rcases hz with hz|hz
        · have hh : z ∈ A ∪ B := Or.inl hz
          rw [hAB] at hh
          change ‖z‖=1 at hh
          simpa only [mem_closedBall,dist_zero_right,hh] using (le_refl (1:ℝ))
        · exact hP hz
      · exact ball_subset_closedBall (hUV (Or.inr hz))
      · rcases hz with hz|hz
        · have hh : z ∈ A ∪ B := Or.inr hz
          rw [hAB] at hh
          change ‖z‖=1 at hh
          simpa only [mem_closedBall,dist_zero_right,hh] using (le_refl (1:ℝ))
        · exact hP hz
    · intro hz
      by_cases hzP : z ∈ P
      · exact Or.inl (Or.inr (Or.inr hzP))
      have hn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
      rcases lt_or_eq_of_le hn with hn|hn
      · have hh : z ∈ U ∪ V := hpart ▸ ⟨by simpa only [mem_ball,dist_zero_right] using hn,hzP⟩
        rcases hh with hh|hh
        · exact Or.inl (Or.inl hh)
        · exact Or.inr (Or.inl hh)
      · have hh : z ∈ A ∪ B := hAB.symm ▸ hn
        rcases hh with hh|hh
        · exact Or.inl (Or.inr (Or.inl hh))
        · exact Or.inr (Or.inr (Or.inl hh))
  · ext z
    constructor
    · rintro ⟨hz,hz'⟩
      rcases hz with hz|hz
      · rcases hz' with hz'|hz'
        · exact False.elim (Set.disjoint_left.mp hdisj hz hz')
        · rcases hz' with hz'|hz'
          · exact False.elim (hABn z (Or.inr hz') (hUV (Or.inl hz)))
          · exact hz'
      · rcases hz with hz|hz
        · rcases hz' with hz'|hz'
          · exact False.elim (hABn z (Or.inl hz) (hUV (Or.inr hz')))
          · rcases hz' with hz'|hz'
            · exact hABP ⟨hz,hz'⟩
            · exact hz'
        · exact hz
    · intro hz
      exact ⟨Or.inr (Or.inr hz),Or.inr (Or.inr hz)⟩

end SLEExactGauge

end

end OAI
