import Mathlib
import OAI.Geometry.WeakMTW.Potentials.PotentialDefinitions

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]
 def hopfLax (t : ℝ) (u : M → ℝ) (z : M) : ℝ := sInf (range (fun x => u x+cost x z/t))
 def ManifoldC11 (f : M → ℝ) : Prop :=
   ContMDiff (model n) 𝓘(ℝ,ℝ) 1 f ∧
     ∀ x : M, ∃ C : ℝ≥0, ∃ U ∈ 𝓝 ((chartAt (Model n) x) x),
       LipschitzOnWith C (fderiv ℝ (fun X : Model n => f ((chartAt (Model n) x).symm X))) U
 def UniformIntermediateGrowth : Prop :=
   ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 → ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧
     ∀ u : M → ℝ, IsPotential u → ∀ t ∈ Icc a b, ∀ q : potentialGraph (n := n) u,
       ∀ x', dist q.val.1 x' < r →
         u q.val.1+cost q.val.1 (potentialProjection u t q)/t+κ*(dist q.val.1 x')^2 ≤
           u x'+cost x' (potentialProjection u t q)/t
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
