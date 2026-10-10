import Mathlib
import OAI.Probability.LatticeSurface.Convexity.Concentration
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityOverlap
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
import OAI.Probability.LatticeSurface.Convexity.EvenIntegral
import OAI.Probability.LatticeSurface.Convexity.GeneralMarginalFin
import OAI.Probability.LatticeSurface.Convexity.LinearConcentration
import OAI.Probability.LatticeSurface.Convexity.MarginalBody
import OAI.Probability.LatticeSurface.Convexity.MarginalOverlap
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.Survival
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCMarginal
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
import OAI.Probability.LatticeSurface.Convexity.Unimodal
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.CompactOverlap
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Density

namespace FacetVolume

end FacetVolume

namespace Overlap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

end Overlap

namespace FacetVolume

end FacetVolume

namespace Density

open FacetVolume

end Density

namespace Density

end Density

namespace Density

end Density

namespace Density

end Density

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace RetainedDensity

end RetainedDensity

namespace RetainedDensity

open MeasureTheory

end RetainedDensity

namespace FacetVolume

end FacetVolume

namespace RetainedDensity

open MeasureTheory

end RetainedDensity

open scoped NNReal ENNReal

namespace Density

open MeasureTheory

end Density

namespace RetainedDensity

theorem compact_convex_marginal_general {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    (K : Set (E × F)) (hK : IsCompact K)
    (hc : Convex ℝ K) (he : ∀ x,x∈K ↔ -x∈K) :
    UpperSemicontinuous (marginal K) ∧ (∀ x,0 ≤ marginal K x) ∧
    Density.LogConcave (marginal K) ∧ (∀ x,marginal K (-x)=marginal K x) ∧
    (∃ R : ℝ,0<R ∧ ∀ x,R<‖x‖ → marginal K x=0) ∧
    (∫ x,marginal K x)=volume.real K := by
  classical
  let e := (Module.finBasis ℝ F).equivFunL
  let d := (ContinuousLinearEquiv.refl ℝ E).prodCongr e
  let H := d '' K
  have hH : IsCompact H := hK.image d.continuous
  have hcH : Convex ℝ H := hc.linear_image d.toLinearMap
  have heH (z) : z∈H ↔ -z∈H := by
    have hi (y) : y∈H ↔ d.symm y∈K := by
      constructor
      · rintro ⟨x,hx,rfl⟩;simpa using hx
      · intro hy;exact ⟨d.symm y,hy,d.apply_symm_apply y⟩
    rw [hi,hi,map_neg]
    exact he _
  obtain ⟨hqu,hq0,hql,hqe,⟨R,hR,hqK⟩,hqmass⟩ := compact_convex_marginal_fin H hH hcH heH
  have : Measure.IsAddHaarMeasure (Measure.map e volume) := e.isAddHaarMeasure_map volume
  let c := Measure.addHaarScalarFactor (Measure.map e volume) (volume : Measure (Fin (Module.finrank ℝ F) → ℝ))
  have hc' : (0:ℝ)<c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmap : Measure.map e volume=(c:ENNReal) • volume := Measure.isAddLeftInvariant_eq_smul _ _
  have hrel (x : E) : marginal K x=(c:ℝ)*marginal H x := by
    have hmeas : Measurable (fun y => H.indicator (fun _ => (1:ℝ)) (x,y)) :=
      (measurable_const.indicator hH.measurableSet).comp (measurable_const.prodMk measurable_id)
    have hh := Density.integral_comp_jacobian e c hmap _ hmeas
    have hi : (fun y => H.indicator (fun _ => (1:ℝ)) (x,e y))=
        (fun y => K.indicator (fun _ => (1:ℝ)) (x,y)) := by
      funext y
      have hm : (x,e y)∈H ↔ (x,y)∈K := by
        change d (x,y)∈d '' K ↔ (x,y)∈K
        exact d.injective.mem_set_image
      by_cases hxy : (x,y)∈K
      · rw [Set.indicator_of_mem (hm.mpr hxy),Set.indicator_of_mem hxy]
      · rw [Set.indicator_of_notMem (mt hm.mp hxy),Set.indicator_of_notMem hxy]
    change (∫ y,K.indicator (fun _ => (1:ℝ)) (x,y))=_
    simpa only [hi,marginal] using hh
  refine ⟨?_,?_,?_,?_,⟨R,hR,?_⟩,?_⟩
  · intro x a ha
    have hh : marginal H x<a/(c:ℝ) := (lt_div_iff₀ hc').mpr (by simpa [hrel,mul_comm] using ha)
    filter_upwards [hqu x _ hh] with y hy
    rw [hrel]
    exact (by nlinarith [(lt_div_iff₀ hc').mp hy])
  · intro x;rw [hrel];exact mul_nonneg hc'.le (hq0 x)
  · intro x y s t hs ht hst
    simp only [hrel]
    calc
      ((c:ℝ)*marginal H x)^s*((c:ℝ)*marginal H y)^t=
          (c:ℝ)*(marginal H x^s*marginal H y^t) := by
        rw [Real.mul_rpow hc'.le (hq0 x),Real.mul_rpow hc'.le (hq0 y)]
        calc
          _ = ((c:ℝ)^s*(c:ℝ)^t)*(marginal H x^s*marginal H y^t) := by ring
          _ = _ := by rw [← Real.rpow_add hc',hst,Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hql x y s t hs ht hst) hc'.le
  · intro x;rw [hrel,hrel,hqe]
  · intro x hx;rw [hrel,hqK x hx,mul_zero]
  · have hi : Integrable (K.indicator (fun _ => (1:ℝ))) :=
      (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
    change (∫ x,∫ z:F,K.indicator (fun _ => (1:ℝ)) (x,z))=volume.real K
    rw [← integral_prod _ hi]
    exact integral_indicator_one hK.measurableSet

end RetainedDensity

end
end
end

end OAI
