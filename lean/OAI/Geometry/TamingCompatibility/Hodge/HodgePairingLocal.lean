import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothSpatial
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgePairingHeat

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingEvaluation_smul_of (a b : PreL2 A J α hs ht true) (x : X) (c : ℝ)
    (hab : a.val x = c • b.val x) : C.pairingEvaluation a x = c • C.pairingEvaluation b x := by
  have hp (i : C.centers) (j : Fin 6) :
      GeometricAdjoint.pairing J α ht a.val (C.basisForm i j).val x =
        c * GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x := by
    change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
      (a.val x : MetricForms.Form Space 2) ((C.basisForm i j).val x : MetricForms.Form Space 2) =
      c * MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
        (b.val x : MetricForms.Form Space 2) ((C.basisForm i j).val x : MetricForms.Form Space 2)
    erw [hab,MetricForms.pairing_smul_left]
  simp only [pairingEvaluation,pairingEvaluationTerm,hp,Finset.smul_sum,smul_smul]

lemma pairingEvaluationVector_smul_of (a b : PreL2 A J α hs ht true) (x : X) (c : ℝ)
    (hab : a.val x = c • b.val x) :
    C.pairingEvaluationVector a x = c • C.pairingEvaluationVector b x := by
  unfold pairingEvaluationVector
  rw [C.pairingEvaluation_smul_of a b x c hab]
  simp only [map_smul,_root_.smul_apply]

lemma pairingHeatVector_smul_of (a b : PreL2 A J α hs ht true) (x : X) (c : ℝ)
    (hab : a.val x = c • b.val x) :
    C.pairingHeatVector a x = c • C.pairingHeatVector b x := by
  unfold pairingHeatVector pairingHeatEvaluation
  rw [C.pairingEvaluation_smul_of a b x c hab,ContinuousLinearMap.smul_comp]
  simp only [map_smul,_root_.smul_apply]

lemma pairingGammaTail_smul_of (T : ℝ) (hT : 0 ≤ T) (s : ℝ)
    (a a' b b' : PreL2 A J α hs ht true) (x y : X) (c d : ℝ)
    (ha : a'.val y = c • a.val y) (hb : b'.val x = d • b.val x) :
    C.pairingGammaTail T hT s a' b' x y = d*c*C.pairingGammaTail T hT s a b x y := by
  unfold pairingGammaTail
  rw [C.pairingHeatVector_smul_of b' b x d hb,C.pairingHeatVector_smul_of a' a y c ha,
    map_smul,real_inner_smul_left,real_inner_smul_right,mul_assoc]

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
