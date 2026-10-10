import OAI.Geometry.RCD.Transport.CompactCouplingLift
import OAI.Analysis.RCDHeat.Foundations
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Compact subtype cost minimizers are ambient optimal couplings -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  {S T : Set X} [CompactSpace S] [CompactSpace T]

theorem compact_coupling_transportCost (Q : Measure (S × T)) [IsFiniteMeasure Q] :
    transportCost (Q.map (Prod.map Subtype.val Subtype.val)) =
      ENNReal.ofReal (∫ z, dist (z.1 : X) (z.2 : X)^2 ∂Q) := by
  have hm : Measurable (fun z : X × X => ENNReal.ofReal (dist z.1 z.2)^2) := by fun_prop
  rw [transportCost,lintegral_map hm (measurable_subtype_coe.prodMap measurable_subtype_coe)]
  have hi : Integrable (fun z : S × T => dist (z.1 : X) (z.2 : X)^2) Q :=
    (by fun_prop : Continuous (fun z : S × T => dist (z.1 : X) (z.2 : X)^2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro z
  exact (ENNReal.ofReal_pow dist_nonneg 2).symm

theorem compact_coupling_ambient_optimal (hS : MeasurableSet S) (hT : MeasurableSet T)
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (S × T)) [IsProbabilityMeasure Q]
    (hl : Q.map Prod.fst=μ) (hr : Q.map Prod.snd=ν)
    (hmin : ∀ P : Measure (S × T), P.map Prod.fst=μ → P.map Prod.snd=ν →
      (∫ z, dist (z.1 : X) (z.2 : X)^2 ∂Q) ≤ ∫ z, dist (z.1 : X) (z.2 : X)^2 ∂P) :
    IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (Q.map (Prod.map Subtype.val Subtype.val)) := by
  have hm : Measurable (Prod.map (Subtype.val : S → X) (Subtype.val : T → X)) :=
    measurable_subtype_coe.prodMap measurable_subtype_coe
  refine ⟨?_,?_,?_⟩
  · rw [Measure.map_map measurable_fst hm,← hl,
      Measure.map_map measurable_subtype_coe measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd hm,← hr,
      Measure.map_map measurable_subtype_coe measurable_snd]
    rfl
  · intro π hπl hπr
    obtain ⟨P,hP,hPl,hPr⟩ := coupling_lift_subtypes hS hT μ ν π hπl hπr
    let : IsProbabilityMeasure (P.map Prod.fst) := by rw [hPl]; infer_instance
    let : IsProbabilityMeasure P := Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
    rw [← hP,compact_coupling_transportCost Q,compact_coupling_transportCost P]
    exact ENNReal.ofReal_le_ofReal (hmin P hPl hPr)

end RegularPointCoordinates

end

end OAI
