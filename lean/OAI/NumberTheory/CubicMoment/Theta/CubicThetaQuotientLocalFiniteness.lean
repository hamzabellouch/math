import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalQuotientMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointMeasureLocallyFinite

namespace OAI

/-! The quotient's actual hyperbolic measure is locally finite. Small
compact neighborhoods are lifted through the proved covering charts. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

instance cubicThetaQuotientMeasure_locallyFinite : IsLocallyFiniteMeasure cubicThetaQuotientMeasure where
  finiteAtNhds q := by
    let p := cubicThetaQuotientLift q
    let e := cubicThetaCoveringChart p
    obtain ⟨K,hK,hpK,hKe⟩ := exists_compact_subset e.open_source (cubicThetaCoveringChart_source p)
    refine ⟨cubicThetaQuotientMap '' K,?_,?_⟩
    · have h := cubicThetaQuotientMap_open.isOpenMap.image_mem_nhds
        (mem_interior_iff_mem_nhds.mp hpK)
      rwa [cubicThetaQuotientLift_map] at h
    · rw [cubicThetaQuotientMeasure_chart e (cubicThetaCoveringChart_coe p)
        hK.isClosed.measurableSet hKe]
      exact cubicThetaPointMeasure_compact hK

instance cubicThetaQuotientMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts cubicThetaQuotientMeasure :=
  inferInstance

end CubicFirstMoment

end

end OAI
