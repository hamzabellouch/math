import OAI.Geometry.NodalSets.Elliptic.SeedCoordAdmissibility

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma seedCoordMetric_smooth (c : BaseModel → CoefficientPoint BaseModel)
    (hc : ContDiff ℝ ∞ c)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α)) :
    ContDiff ℝ ∞ (seedCoordMetric c) := by
  have hm : ContDiff ℝ ∞ (coefficientMetricValue ∘ c) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (coefficientMetricValue_smoothAt (c y) (positiveContravariantEquiv (c y).1 (hp y)) rfl).comp y hc.contDiffAt
  have hh := (contDiff_const (c := seedCoordEquiv.toContinuousLinearMap.precomp ℝ)).clm_comp
    ((hm.comp seedCoordEquiv.contDiff).clm_comp
      (contDiff_const (c := seedCoordEquiv.toContinuousLinearMap)))
  convert hh using 1
  funext x
  ext u v
  rfl

lemma seedCoordMetric_positive (c : BaseModel → CoefficientPoint BaseModel)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α))
    (hρ : ∀ y, 0 < (c y).2) (x : Coord) (v : Coord) (hv : v ≠ 0) :
    0 < seedCoordMetric c x v v :=
  linearMetricField_positive seedCoordEquiv (coefficientMetricValue ∘ c) x
    (coefficientMetric_positive (c (seedCoordEquiv x)) (hp _) (hρ _)) v hv

lemma seedCoordMetric_symmetric (c : BaseModel → CoefficientPoint BaseModel)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α))
    (hs : ∀ y (α β : BaseModel →L[ℝ] ℝ), α ((c y).1 β) = β ((c y).1 α))
    (x u v : Coord) : seedCoordMetric c x u v = seedCoordMetric c x v u :=
  coefficientMetric_symmetric (c (seedCoordEquiv x)) (hp _) (hs _) _ _

end
end Yau.Target

end OAI
