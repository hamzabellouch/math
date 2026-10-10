import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateUniformLipschitz
import OAI.Geometry.WeakMTW.Potentials.IntermediateAtlas

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def IntermediateGeometry (hMTW : HasWeakMTW (n := n) (M := M)) : Prop :=
   (∀ u v : M → ℝ, ∀ huv : IsDualPair u v, ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht1 : t < 1,
     (∀ z, hopfLax t u z = -hopfLax (1-t) v z) ∧ ManifoldC11 (n := n) (hopfLax t u) ∧
       ∀ z : M,
         intermediateInverse hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1 z =
           geodesicFlow (-t) (⟨z,normalGradient (hopfLax t u) z⟩ : TangentBundle (model n) M) ∧
         (intermediateInverse hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1 z).1 =
           exp (n := n) z ((-t) • normalGradient (hopfLax t u) z)) ∧
   UniformIntermediateC11 (n := n) (M := M) ∧ UniformIntermediateLipschitz hMTW ∧
   UniformIntermediateGrowth (n := n) (M := M)
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
