import Mathlib

namespace OAI

open Set MeasureTheory

namespace UnitControl

noncomputable def law : Measure (Icc (0:ℝ) 1) := Measure.comap Subtype.val volume

instance : IsProbabilityMeasure law := by
  constructor
  rw [law,(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume univ]
  rw [Set.image_univ,Subtype.range_coe]
  norm_num

lemma support_full (t : Icc (0:ℝ) 1) : t∈law.support := by
  rw [Measure.mem_support_iff_forall]
  intro S hS
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hS
  apply lt_of_lt_of_le _ (measure_mono hball)
  rw [law,(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply volume (Metric.ball t ε)]
  have he : Subtype.val '' Metric.ball t ε=Icc (0:ℝ) 1∩Ioo ((t:ℝ)-ε) ((t:ℝ)+ε) := by
    ext x
    simp only [mem_image,Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_sub_lt_iff,mem_inter_iff,mem_Icc,mem_Ioo]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,by constructor <;> linarith⟩
    · rintro ⟨hx,hlo,hhi⟩
      exact ⟨⟨x,hx⟩,⟨by linarith,by linarith⟩,rfl⟩
  rw [he]
  have hmax : max 0 ((t:ℝ)-ε)< min 1 ((t:ℝ)+ε) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    constructor <;> constructor <;> linarith [t.property.1,t.property.2]
  apply lt_of_lt_of_le (show 0<volume (Ioo (max 0 ((t:ℝ)-ε)) (min 1 ((t:ℝ)+ε))) by simpa using ENNReal.ofReal_pos.mpr (sub_pos.mpr hmax)) (measure_mono _)
  intro x hx
  exact ⟨⟨le_of_lt ((le_max_left _ _).trans_lt hx.1),le_of_lt (hx.2.trans_le (min_le_left _ _))⟩,
    ⟨(le_max_right _ _).trans_lt hx.1,hx.2.trans_le (min_le_right _ _)⟩⟩

lemma map_val : Measure.map Subtype.val law=volume.restrict (Icc (0:ℝ) 1) := by
  exact map_comap_subtype_coe measurableSet_Icc volume

end UnitControl

end OAI
