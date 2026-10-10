import OAI.Probability.SLE.Geometry.HalfDiskGeometry

namespace OAI

/-! The full circle and its two half-disk Jordan regions. -/
noncomputable section
open Set Complex Metric
open scoped ComplexConjugate

namespace SLEExactGauge

lemma diskLowerArc_continuous : Continuous diskLowerArc :=
  Complex.continuous_conj.comp diskUpperArc_continuous

lemma diskLowerArc_injOn : InjOn diskLowerArc (Icc 0 1) := by
  intro s hs t ht he
  exact diskUpperArc_injOn hs ht (Complex.conjCLE.injective he)

lemma diskLowerArc_zero : diskLowerArc 0 = -1 := by
  simp [diskLowerArc,diskUpperArc_zero]

lemma diskLowerArc_one : diskLowerArc 1 = 1 := by
  simp [diskLowerArc,diskUpperArc_one]

theorem disk_circle_jordan :
    Schoenflies.IsJordanCurve (complexPlaneCoordinates '' {z : ℂ | ‖z‖=1}) := by
  rw [← disk_semicircle_union,image_union]
  have hA := complexPlaneCoordinates_isArcBetween diskUpperArc
    diskUpperArc_continuous.continuousOn diskUpperArc_injOn
  have hB := complexPlaneCoordinates_isArcBetween diskLowerArc
    diskLowerArc_continuous.continuousOn diskLowerArc_injOn
  rw [diskLowerArc_zero,diskLowerArc_one,← diskUpperArc_zero,← diskUpperArc_one] at hB
  apply Schoenflies.isJordanCurve_union hA hB
  rintro _ ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
  have hab := complexPlaneCoordinates.injective he
  have hz : a ∈ ({-1,1}:Set ℂ) := by
    rw [← disk_semicircle_inter]
    exact ⟨ha,hab ▸ hb⟩
  rcases hz with hz|hz
  · left
    rw [hz,diskUpperArc_zero]
  · right
    rw [hz,diskUpperArc_one]

theorem complexInside_unitDisk :
    complexInside {z : ℂ | ‖z‖=1} = ball (0:ℂ) 1 := by
  apply complexInside_eq_open disk_circle_jordan isOpen_ball
    (convex_ball _ _).isPreconnected (nonempty_ball.mpr (by norm_num))
    isBounded_ball
  rw [frontier_ball _ (by norm_num : (1:ℝ)≠0)]
  ext z
  simp

def openLowerDisk : Set ℂ := {z | ‖z‖ < 1 ∧ z.im < 0}
def closedLowerDisk : Set ℂ := {z | ‖z‖ ≤ 1 ∧ z.im ≤ 0}

lemma conj_image_openUpperDisk : conj '' openUpperDisk=openLowerDisk := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa [openUpperDisk,openLowerDisk] using hw
  · intro hz
    refine ⟨conj z,?_,Complex.conj_conj z⟩
    simpa [openUpperDisk,openLowerDisk] using hz

lemma conj_image_closedUpperDisk : conj '' closedUpperDisk=closedLowerDisk := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa [closedUpperDisk,closedLowerDisk] using hw
  · intro hz
    refine ⟨conj z,?_,Complex.conj_conj z⟩
    simpa [closedUpperDisk,closedLowerDisk] using hz

lemma openLowerDisk_closure : closure openLowerDisk=closedLowerDisk := by
  have hh := Complex.conjCLE.toHomeomorph.image_closure openUpperDisk
  change conj '' closure openUpperDisk=closure (conj '' openUpperDisk) at hh
  rw [openUpperDisk_closure,conj_image_openUpperDisk,conj_image_closedUpperDisk] at hh
  exact hh.symm

lemma conj_image_diskDiameter : conj '' (diskDiameter '' Icc 0 1)=diskDiameter '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨_,⟨s,hs,rfl⟩,rfl⟩
    simpa only [diskDiameter,Complex.conj_ofReal] using mem_image_of_mem diskDiameter hs
  · rintro ⟨s,hs,rfl⟩
    refine ⟨diskDiameter s,mem_image_of_mem _ hs,?_⟩
    exact Complex.conj_ofReal _

theorem complexInside_lowerDisk :
    complexInside (diskDiameter '' Icc 0 1 ∪ diskLowerArc '' Icc 0 1)=openLowerDisk := by
  have he : conj '' (diskUpperArc '' Icc 0 1)=diskLowerArc '' Icc 0 1 := by
    rw [image_image]
    rfl
  have hh := complexInside_transport Complex.conjCLE.toHomeomorph
    (diskDiameter '' Icc 0 1 ∪ diskUpperArc '' Icc 0 1)
  change conj '' complexInside (diskDiameter '' Icc 0 1 ∪ diskUpperArc '' Icc 0 1)=
    complexInside (conj '' (diskDiameter '' Icc 0 1 ∪ diskUpperArc '' Icc 0 1)) at hh
  rw [image_union,conj_image_diskDiameter,he,complexInside_upperDisk,
    conj_image_openUpperDisk] at hh
  exact hh.symm

lemma closed_halfDisks_union : closedUpperDisk ∪ closedLowerDisk=closedBall (0:ℂ) 1 := by
  ext z
  simp only [mem_union,closedUpperDisk,closedLowerDisk,mem_ofPred,mem_closedBall,dist_zero_right]
  constructor
  · rintro (h|h) <;> exact h.1
  · intro hz
    rcases le_total 0 z.im with hi|hi
    · exact Or.inl ⟨hz,hi⟩
    · exact Or.inr ⟨hz,hi⟩

lemma closed_halfDisks_inter :
    closedUpperDisk ∩ closedLowerDisk=diskDiameter '' Icc 0 1 := by
  rw [diskDiameter_image]
  ext z
  simp only [closedUpperDisk,closedLowerDisk,mem_inter_iff,mem_ofPred]
  constructor
  · rintro ⟨hp,hm⟩
    exact ⟨hp.1,le_antisymm hm.2 hp.2⟩
  · rintro ⟨hn,hi⟩
    exact ⟨⟨hn,hi.ge⟩,⟨hn,hi.le⟩⟩

end SLEExactGauge

end

end OAI
