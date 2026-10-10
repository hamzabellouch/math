import OAI.Geometry.Relativity.CKS.CollarExpansionInputNorm
import OAI.Geometry.Relativity.CKS.MixedMatrixJets
import OAI.Geometry.Relativity.CKS.RoundReferenceJets

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actualScalarJet_continuousAt {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    ContinuousAt (actualScalarJet f) x := by
  apply ContinuousAt.prodMk hf.continuousAt
  apply ContinuousAt.prodMk
  · apply continuousAt_pi.mpr
    intro a
    exact (contDiffAt_D hf (m := 1) (by norm_num) (basis a)).continuousAt
  · apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro b
    exact (contDiffAt_D (contDiffAt_D hf (m := 1) (by norm_num) (basis b))
      (m := 0) (by norm_num) (basis a)).continuousAt

lemma actualThreeJet_continuousAt {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    ContinuousAt (actualThreeJet f) x := by
  apply ContinuousAt.prodMk (actualScalarJet_continuousAt (hf.of_le (by norm_num)))
  apply continuousAt_pi.mpr
  intro a
  exact actualScalarJet_continuousAt (contDiffAt_D hf (by norm_num) (basis a))

lemma matrixThreeJets_continuous {q : Point → Mat} (hq : ContDiff ℝ 3 q) :
    Continuous (matrixThreeJets q) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  exact actualThreeJet_continuousAt (component_three hq.contDiffAt i k)

def roundShiftReference (x : Point) : ShiftInput := (matrixThreeJets stereoMetric x,0)
def roundShiftFamily (c : ℝ) : Set ShiftInput := roundShiftReference '' Metric.closedBall 0 c

def roundExpansionReference (x : Point) : ExpansionInput :=
  packExpansion (matrixThreeJets stereoMetric x) 0 0
def roundExpansionFamily (c : ℝ) : Set ExpansionInput := roundExpansionReference '' Metric.closedBall 0 c

lemma roundShiftReference_continuous : Continuous roundShiftReference :=
  (matrixThreeJets_continuous (stereoMetric_smooth.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).prodMk continuous_const

lemma roundShiftFamily_compact (c : ℝ) : IsCompact (roundShiftFamily c) :=
  (isCompact_closedBall 0 c).image roundShiftReference_continuous

lemma roundShiftFamily_regular (c : ℝ) : roundShiftFamily c ⊆ shiftRegion := by
  rintro j ⟨x,hx,rfl⟩
  exact (stereoMetric_det_positive x).ne'

lemma roundExpansionReference_continuous : Continuous roundExpansionReference := by
  have hp : Continuous (fun q : MatrixThreeJet => packExpansion q 0 0) := by
    unfold packExpansion
    fun_prop
  exact hp.comp (matrixThreeJets_continuous (stereoMetric_smooth.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))

lemma roundExpansionFamily_compact (c : ℝ) : IsCompact (roundExpansionFamily c) :=
  (isCompact_closedBall 0 c).image roundExpansionReference_continuous

lemma roundExpansionFamily_regular (c : ℝ) : roundExpansionFamily c ⊆ expansionRegion := by
  rintro j ⟨x,hx,rfl⟩
  exact (stereoMetric_det_positive x).ne'

end
end CKSAngularGeometry

end

end OAI
