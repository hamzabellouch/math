import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairingIntegral

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingEvaluation_star (b : PreL2 A J α hs ht true) (x : X) :
    C.pairingEvaluation (preStar A J α hs ht b) x =
      (C.pairingEvaluation b x).comp (l2Star A J α hs ht) := by
  have he : (fun f => C.pairingEvaluation (preStar A J α hs ht b) x f) =
      (fun f => C.pairingEvaluation b x (l2Star A J α hs ht f)) :=
    (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr).equalizer
      (C.pairingEvaluation (preStar A J α hs ht b) x).continuous
      ((C.pairingEvaluation b x).continuous.comp (l2Star A J α hs ht).continuous) (by
        funext a
        dsimp only [Function.comp_apply]
        have h := hodgeRegularization_smoothShift_cube A J α hs ht r hr a
        have hstar : hodgeRegularization A J α hs ht r
            (l2Star A J α hs ht (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a))) =
            smoothL2 A J α hs ht true (preStar A J α hs ht a) := by
          rw [hodgeRegularization_star,h,l2Star_smooth]
        rw [C.pairingEvaluation_smooth _ _ _ a h,
          C.pairingEvaluation_smooth _ _ _ (preStar A J α hs ht a) hstar]
        exact hodgeStar_pairing J α ht b.val a.val x)
  ext f
  exact congrFun he f

lemma pairingEvaluationVector_star (b : PreL2 A J α hs ht true) (x : X) :
    C.pairingEvaluationVector (preStar A J α hs ht b) x =
      l2Star A J α hs ht (C.pairingEvaluationVector b x) := by
  apply ext_inner_right ℝ
  intro f
  rw [l2Star_self_adjoint]
  simp only [pairingEvaluationVector,ContinuousLinearMap.adjoint_inner_left,
    Real.inner_apply,one_mul]
  exact congrArg (fun L : L2 A J α hs ht true →L[ℝ] ℝ => L f) (C.pairingEvaluation_star b x)

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
