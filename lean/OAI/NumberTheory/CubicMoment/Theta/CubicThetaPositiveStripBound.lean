import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCompact

namespace OAI

/-! Bounded multiplicity of a positive-height period strip over the
actual arithmetic quotient. Only a finite compact chart cover is used. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaCompact_pullback_bound {K : Set CubicThetaPoint} (hK : IsCompact K) :
    ∃ N : ℕ,(cubicThetaPointMeasure.restrict K).map cubicThetaQuotientMap≤
      (N:ℝ≥0∞) • cubicThetaQuotientMeasure := by
  classical
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover
    (fun p => (cubicThetaCoveringChart p).source)
    (fun p => (cubicThetaCoveringChart p).open_source) (by
      intro p _
      exact mem_iUnion.mpr ⟨p,cubicThetaCoveringChart_source p⟩)
  refine ⟨T.card,Measure.le_iff.mpr (fun B hB => ?_)⟩
  rw [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable),
    Measure.smul_apply,smul_eq_mul]
  calc
    cubicThetaPointMeasure (cubicThetaQuotientMap ⁻¹' B ∩ K)≤
        cubicThetaPointMeasure (⋃ p∈T,
          cubicThetaQuotientMap ⁻¹' B ∩ (cubicThetaCoveringChart p).source) := by
      apply measure_mono
      rintro p ⟨hB,hK⟩
      obtain ⟨q,hq,hp⟩ := mem_iUnion₂.mp (hT hK)
      exact mem_iUnion₂.mpr ⟨q,hq,hB,hp⟩
    _ ≤ ∑ p∈T,cubicThetaPointMeasure
        (cubicThetaQuotientMap ⁻¹' B ∩ (cubicThetaCoveringChart p).source) :=
      measure_biUnion_finset_le T _
    _ ≤ ∑ _p∈T,cubicThetaQuotientMeasure B := by
      apply Finset.sum_le_sum
      intro p _
      have hm := cubicThetaChart_measure_le (cubicThetaCoveringChart p)
        (cubicThetaCoveringChart_coe p) (cubicThetaCoveringChart p).open_source.measurableSet
        (Subset.rfl)
      have hb := hm B
      simpa only [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
        Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable)] using hb
    _ = _ := by simp [nsmul_eq_mul]

lemma cubicThetaPositiveStrip_compact_cover {ε : ℝ} (hε : 0<ε) :
    ∃ K : Set CubicThetaPoint,IsCompact K ∧
      cubicThetaCuspStrip ε⊆K ∪ cubicThetaCuspStrip 2 := by
  obtain ⟨L,hL,hcell⟩ := cubicThetaHorizontalCell_compact_container
  let B : Set (ℂ × ℝ) := L ×ˢ Icc ε 2
  have hpos : B⊆{y : ℂ × ℝ | 0<y.2} := fun y hy => hε.trans_le hy.2.1
  have hc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  refine ⟨cubicThetaPointInclusion.symm '' B,
    (hL.prod isCompact_Icc).image_of_continuousOn (hc.mono hpos),?_⟩
  intro p hp
  by_cases hv : 2<p.val.2
  · exact Or.inr ⟨hv,hp.2⟩
  · apply Or.inl
    refine ⟨p.val,⟨hcell hp.2,hp.1.le,le_of_not_gt hv⟩,?_⟩
    exact cubicThetaPointInclusion.left_inv
      (by rw [cubicThetaPointInclusion_source]; trivial)

theorem cubicThetaPositiveStrip_pullback_bound {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ,0<N ∧
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)).map cubicThetaQuotientMap≤
        (N:ℝ≥0∞) • cubicThetaQuotientMeasure := by
  obtain ⟨K,hK,hcover⟩ := cubicThetaPositiveStrip_compact_cover hε
  obtain ⟨N,hN⟩ := cubicThetaCompact_pullback_bound hK
  refine ⟨N+1,by omega,Measure.le_iff.mpr (fun B hB => ?_)⟩
  have hq := cubicThetaQuotientMap_open.continuous.measurable
  have hpre := hB.preimage hq
  have hN' := hN B
  rw [Measure.map_apply hq hB,Measure.restrict_apply hpre,
    Measure.smul_apply,smul_eq_mul] at hN' ⊢
  have hhigh := (Measure.restrict_le_self (μ:=cubicThetaQuotientMeasure)
    (s:=cubicThetaQuotientMap '' cubicThetaCuspStrip 2)) B
  rw [←cubicThetaInjective_map_restrict (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)),Measure.map_apply hq hB,
    Measure.restrict_apply hpre] at hhigh
  calc
    cubicThetaPointMeasure (cubicThetaQuotientMap ⁻¹' B ∩ cubicThetaCuspStrip ε)≤
        cubicThetaPointMeasure ((cubicThetaQuotientMap ⁻¹' B ∩ K) ∪
          (cubicThetaQuotientMap ⁻¹' B ∩ cubicThetaCuspStrip 2)) := by
      apply measure_mono
      rintro p ⟨hb,hp⟩
      rcases hcover hp with hk|hh
      · exact Or.inl ⟨hb,hk⟩
      · exact Or.inr ⟨hb,hh⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ (N:ℝ≥0∞)*cubicThetaQuotientMeasure B+cubicThetaQuotientMeasure B :=
      add_le_add hN' hhigh
    _ = _ := by rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul]

end CubicFirstMoment

end

end OAI
