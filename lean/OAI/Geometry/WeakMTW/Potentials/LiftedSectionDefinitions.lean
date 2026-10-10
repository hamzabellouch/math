import Mathlib
import OAI.Geometry.WeakMTW.Domains.Definitions

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 def liftedGap (u v : M → ℝ) (x : M) (p : TangentSpace (model n) x) : ℝ :=
   u x+‖p‖^2/2+v (exp x p)
 def liftedGapSection (u v : M → ℝ) (x : M) (r : ℝ) : Set (TangentSpace (model n) x) :=
   {p | p ∈ minimizingDomain x ∧ liftedGap u v x p ≤ r}
 def sectionOscillation (v : M → ℝ) (x : M) (S : Set (TangentSpace (model n) x)) : ℝ :=
   sSup ((fun p => v (exp x p)) '' S)-sInf ((fun p => v (exp x p)) '' S)
 def ConvexLiftedSections (u v : M → ℝ) : Prop :=
   ∀ x : M, ∀ r : ℝ, IsCompact (liftedGapSection (n := n) u v x r) ∧
     Convex ℝ (liftedGapSection (n := n) u v x r) ∧
     ((liftedGapSection (n := n) u v x r).Nonempty → 0 ≤ r →
       (Metric.diam (liftedGapSection (n := n) u v x r))^2 ≤
         8*(r+sectionOscillation (n := n) v x (liftedGapSection (n := n) u v x r)))
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
