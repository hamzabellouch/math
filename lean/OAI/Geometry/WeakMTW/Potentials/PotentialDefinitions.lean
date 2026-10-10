import Mathlib
import OAI.Geometry.WeakMTW.Domains.Definitions

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 def cTransform (v : M → ℝ) (x : M) : ℝ := sSup (Set.range (fun y => -cost x y-v y))
 def IsPotential (u : M → ℝ) : Prop := ∃ v : M → ℝ, Continuous v ∧ u = cTransform v
 def IsDualPair (u v : M → ℝ) : Prop :=
   Continuous u ∧ Continuous v ∧ u = cTransform v ∧ v = cTransform u
 def ordinarySubdiff (u : M → ℝ) (x : M) : Set (TangentSpace (model n) x) :=
   {p | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : TangentSpace (model n) x,
     ‖h‖ < δ → u x + inner ℝ p h - ε*‖h‖ ≤ u (exp x h)}
 def potentialGraph (u : M → ℝ) : Set (TangentBundle (model n) M) :=
   {q | q.2 ∈ ordinarySubdiff u q.1}
 def potentialProjection (u : M → ℝ) (t : ℝ) (q : potentialGraph (n := n) u) : M :=
   exp q.val.1 (t•q.val.2)
 def GlobalSupportingProperty (u : M → ℝ) : Prop :=
   (∀ x (p : TangentSpace (model n) x), p ∈ ordinarySubdiff u x →
     p ∈ minimizingDomain x ∧ ∀ x', u x + cost x (exp x p)-cost x' (exp x p) ≤ u x') ∧
   ∀ t : ℝ, 0 < t → t < 1 →
     IsHomeomorph (potentialProjection (n := n) u t) ∧
     ∀ (q : potentialGraph (n := n) u),
       t•q.val.2 ∈ injectivityDomain q.val.1 ∧
       ∀ x', u q.val.1 + cost q.val.1 (potentialProjection u t q)/t ≤
         u x' + cost x' (potentialProjection u t q)/t ∧
         (u x' + cost x' (potentialProjection u t q)/t =
           u q.val.1 + cost q.val.1 (potentialProjection u t q)/t → x' = q.val.1)
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
