import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Chart Submersion. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.AlignedProductChart
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]

lemma snd_mfderiv_surjective (P : AlignedProductChart S A B) {x : X.Carrier}
    (hx : x∈P.chart.source) :
    Function.Surjective (mfderiv (ModelWithCorners X) 𝓘(ℂ,B) (fun y => (P.chart y).2) x) := by
  change Function.Surjective (mfderiv (ModelWithCorners X) 𝓘(ℂ,B)
    ((ContinuousLinearMap.snd ℂ A B) ∘ P.chart) x)
  rw [mfderiv_comp x (ContinuousLinearMap.snd ℂ A B).mdifferentiableAt
    ((P.holomorphicAt hx).mdifferentiableAt (by simp)),mfderiv_eq_fderiv,
    ContinuousLinearMap.fderiv]
  exact Prod.snd_surjective.comp (P.mdifferentiable.mfderiv_surjective hx)

end SplitTangent.AlignedProductChart

end

end OAI
