import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeAction
import Mathlib.Geometry.Manifold.ChartedSpace

namespace OAI

/-! Concrete local coordinate charts for the principal quotient, obtained
from the proved covering map and the open positive-height half-space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

private def positiveHeightOpen : TopologicalSpace.Opens (ℂ × ℝ) :=
  ⟨{p | 0<p.2},isOpen_lt continuous_const continuous_snd⟩

def cubicThetaPointInclusion : OpenPartialHomeomorph CubicThetaPoint (ℂ × ℝ) :=
  positiveHeightOpen.openPartialHomeomorphSubtypeCoe ⟨⟨(0,1),by change (0:ℝ)<1; norm_num⟩⟩

lemma cubicThetaPointInclusion_coe :
    (cubicThetaPointInclusion : CubicThetaPoint → ℂ × ℝ)=Subtype.val := rfl

lemma cubicThetaPointInclusion_source : cubicThetaPointInclusion.source=Set.univ := rfl

lemma cubicThetaPointInclusion_target :
    cubicThetaPointInclusion.target={p : ℂ × ℝ | 0<p.2} := by
  exact positiveHeightOpen.openPartialHomeomorphSubtypeCoe_target _

def cubicThetaQuotientLift (q : CubicThetaQuotient) : CubicThetaPoint :=
  Classical.choose (cubicThetaQuotientMap_surjective q)

lemma cubicThetaQuotientLift_map (q : CubicThetaQuotient) :
    cubicThetaQuotientMap (cubicThetaQuotientLift q)=q :=
  Classical.choose_spec (cubicThetaQuotientMap_surjective q)

def cubicThetaCoveringChart (p : CubicThetaPoint) :
    OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient :=
  Classical.choose (cubicThetaQuotient_localHomeomorph p)

lemma cubicThetaCoveringChart_source (p : CubicThetaPoint) :
    p∈(cubicThetaCoveringChart p).source :=
  (Classical.choose_spec (cubicThetaQuotient_localHomeomorph p)).1

lemma cubicThetaCoveringChart_coe (p : CubicThetaPoint) :
    (cubicThetaCoveringChart p : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap :=
  (Classical.choose_spec (cubicThetaQuotient_localHomeomorph p)).2.symm

def cubicThetaQuotientChart (q : CubicThetaQuotient) :
    OpenPartialHomeomorph CubicThetaQuotient (ℂ × ℝ) :=
  (cubicThetaCoveringChart (cubicThetaQuotientLift q)).symm.trans cubicThetaPointInclusion

lemma cubicThetaQuotientChart_source (q : CubicThetaQuotient) :
    q∈(cubicThetaQuotientChart q).source := by
  let p := cubicThetaQuotientLift q
  have hp := (cubicThetaCoveringChart p).map_source (cubicThetaCoveringChart_source p)
  rw [cubicThetaCoveringChart_coe,cubicThetaQuotientLift_map] at hp
  exact ⟨hp,by rw [cubicThetaPointInclusion_source]; trivial⟩

instance cubicThetaQuotient_chartedSpace : ChartedSpace (ℂ × ℝ) CubicThetaQuotient where
  atlas := Set.range cubicThetaQuotientChart
  chartAt := cubicThetaQuotientChart
  mem_chart_source := cubicThetaQuotientChart_source
  chart_mem_atlas q := ⟨q,rfl⟩

end CubicFirstMoment

end

end OAI
