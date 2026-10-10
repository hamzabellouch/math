import OAI.Geometry.NodalSets.Elliptic.WeightedLift

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma circleLift_smooth (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) :
    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift f) :=
  hf.comp contMDiff_fst

lemma circleLift_nonzero (f : Base → ℝ) (hf : f ≠ 0) : circleLift f ≠ 0 := by
  intro h
  apply hf
  funext x
  exact congrFun h (x,1)

lemma independentAmbientMetric_eigenfunction_lift
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (hf0 : f ≠ 0)
    (lam : ℝ)
    (he : ∀ x : Base, -ambientWeightedChartOperator A rho f x (extChartAt (𝓡 4) x x) = lam * f x) :
    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift f) ∧ circleLift f ≠ 0 ∧
      ∀ x : Manifold5, -chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
        (extChartAt modelWithCorners x) (circleLift f) (extChartAt modelWithCorners x x) =
          lam * circleLift f x := by
  refine ⟨circleLift_smooth f hf,circleLift_nonzero f hf0,fun x ↦ ?_⟩
  rw [independentAmbientMetric_weighted_lift A rho hA hp hr hrp hrad f hf x
    ((extChartAt modelWithCorners x).map_source (mem_extChartAt_source x))]
  exact he x.1

end
end Yau.Target

end OAI
