import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedPeriodMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexIntegrability

namespace OAI

/-! Compact height windows in the actual period-nine cusp cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaShiftedWindow (a d : ℝ) : Set CubicThetaPoint :=
  {p | p.val.1∈cubicThetaShiftedHorizontalCell ∧ p.val.2∈Icc a d}

lemma cubicThetaShiftedWindow_measurable (a d : ℝ) :
    MeasurableSet (cubicThetaShiftedWindow a d) := by
  have hf : Continuous (fun p : CubicThetaPoint => p.val.1) := by fun_prop
  have hg : Continuous (fun p : CubicThetaPoint => p.val.2) := by fun_prop
  exact (cubicThetaShiftedHorizontalCell_measurable.preimage hf.measurable).inter
    (measurableSet_Icc.preimage hg.measurable)

lemma cubicThetaShiftedWindow_compact_container {a : ℝ} (ha : 0<a) (d : ℝ) :
    ∃ K : Set CubicThetaPoint,IsCompact K ∧ cubicThetaShiftedWindow a d⊆K ∧
      ∀ p∈K,a≤p.val.2 := by
  obtain ⟨L,hL,hcell⟩ := cubicThetaShiftedHorizontalCell_compact_container
  let B : Set (ℂ×ℝ) := L ×ˢ Icc a d
  have hpos : B⊆{y : ℂ×ℝ | 0<y.2} := fun y hy => ha.trans_le hy.2.1
  have hc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ×ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  refine ⟨cubicThetaPointInclusion.symm '' B,
    (hL.prod isCompact_Icc).image_of_continuousOn (hc.mono hpos),?_,?_⟩
  · intro p hp
    refine ⟨p.val,⟨hcell hp.1,hp.2⟩,?_⟩
    exact cubicThetaPointInclusion.left_inv
      (by rw [cubicThetaPointInclusion_source]; trivial)
  · rintro p ⟨y,hy,rfl⟩
    have he := cubicThetaPointInclusion.right_inv
      (show y∈cubicThetaPointInclusion.target by
        rw [cubicThetaPointInclusion_target]; exact hpos hy)
    change (cubicThetaPointInclusion (cubicThetaPointInclusion.symm y)).2≥a
    rw [he]
    exact hy.2.1

lemma cubicThetaShiftedWindow_coordinates {a : ℝ} (ha : 0<a) (d : ℝ) :
    cubicThetaPointCoordinates '' cubicThetaShiftedWindow a d=
      cubicThetaShiftedHorizontalCell ×ˢ Icc a d := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact hp
  · intro hy
    refine ⟨⟨y,ha.trans_le hy.2.1⟩,hy,rfl⟩

lemma cubicThetaShiftedWindow_fubini {a : ℝ} (ha : 0<a) (d : ℝ)
    (f : ℂ×ℝ → ℂ)
    (hf : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure) :
    (∫ p in cubicThetaShiftedWindow a d,f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ v in Icc a d,∫ z in cubicThetaShiftedHorizontalCell,f (z,v)/(v:ℂ)^3 := by
  have hi := (cubicThetaPointIntegrable_complex_density
    (cubicThetaShiftedWindow_measurable a d) f).mp hf
  rw [cubicThetaPointIntegral_complex_density (cubicThetaShiftedWindow_measurable a d),
    cubicThetaShiftedWindow_coordinates ha d]
  rw [cubicThetaShiftedWindow_coordinates ha d] at hi
  change Integrable (fun y : ℂ×ℝ => f y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at hi
  rw [←Measure.prod_restrict] at hi
  change (∫ y : ℂ×ℝ,f y/(y.2:ℂ)^3 ∂
    ((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaShiftedHorizontalCell ×ˢ Icc a d))=_
  rw [←Measure.prod_restrict]
  exact integral_prod_symm _ hi

end CubicFirstMoment

end

end OAI
