import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairingStar
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatIdentification
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgePairingHeat

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

omit [T2Space X] in
lemma hodgeHeatBoost_star {r : ℝ} (hr : 0 < r) (f : L2 A J α hs ht true) :
    hodgeHeatBoost A J α hs ht D hD r (l2Star A J α hs ht f) =
      l2Star A J α hs ht (hodgeHeatBoost A J α hs ht D hD r f) := by
  apply hodgeRegularization_injective A J α hs ht r hr
  have he (v : L2 A J α hs ht true) :
      hodgeRegularization A J α hs ht r (hodgeHeatBoost A J α hs ht D hD r v) =
        hodgeSpectralHeat A J α hs ht D hD (r^2) v :=
    (congrArg (fun L : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => L v)
      (hodgeSpectralHeat_factor A J α hs ht D hD r hr)).symm
  rw [he,hodgeRegularization_star,he,hodgeSpectralHeat_star]

namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingHeatEvaluation_star (b : PreL2 A J α hs ht true) (x : X) :
    C.pairingHeatEvaluation (preStar A J α hs ht b) x =
      (C.pairingHeatEvaluation b x).comp (l2Star A J α hs ht) := by
  ext f
  change C.pairingEvaluation (preStar A J α hs ht b) x (hodgeHeatBoost A J α hs ht D hD r f) =
    C.pairingEvaluation b x (hodgeHeatBoost A J α hs ht D hD r (l2Star A J α hs ht f))
  rw [C.pairingEvaluation_star,ContinuousLinearMap.comp_apply,hodgeHeatBoost_star hr]

lemma pairingHeatVector_star (b : PreL2 A J α hs ht true) (x : X) :
    C.pairingHeatVector (preStar A J α hs ht b) x =
      l2Star A J α hs ht (C.pairingHeatVector b x) := by
  apply ext_inner_right ℝ
  intro f
  rw [l2Star_self_adjoint]
  simp only [pairingHeatVector,ContinuousLinearMap.adjoint_inner_left,Real.inner_apply,one_mul]
  exact congrArg (fun L : L2 A J α hs ht true →L[ℝ] ℝ => L f) (C.pairingHeatEvaluation_star b x)

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
