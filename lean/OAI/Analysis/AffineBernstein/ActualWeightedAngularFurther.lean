import Mathlib
import OAI.Analysis.AffineBernstein.ActualWeightedAngular

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The actual angular weighted drift integrates to exactly `-n/2` times
its nonnegative angular energy. No angular PDE or integration formula is assumed. -/
theorem affineEpigraph_angular_literal_drift {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let N := supportNewtonTensor bE (fun e => H (s,e))
    let dP := fun e => tangentProjection e (gradient (fun y => P (s,y)) e)
    let dF := fun e => tangentProjection e (gradient (fun y => F (s,y)) e)
    let W := fun e => tubeMeasureDensity n H bS bE (s,e)*H (s,e)/tubeAngularDensity H (s,e) bE
    (∫ e : sphere (0:E) 1, W e*roundHessianContraction bE N (fun y => F (s,y)) e ∂volume.toSphere) +
    2*(∫ e : sphere (0:E) 1, W e*N e (dP e) (dF e) ∂volume.toSphere) +
    (∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) =
    (-(n : ℝ)/2)*(∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hw (e : sphere (0:E) 1) :
      Real.exp (2*Real.log (H (s,e))+(((n : ℝ)+2)/2)*invariantTubeF H bS bE
        (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,e)) =
      tubeMeasureDensity n H bS bE (s,e)*H (s,e)/tubeAngularDensity H (s,e) bE := by
    have he : ‖(e:E)‖ = 1 := mem_sphere_zero_iff_norm.1 e.property
    have hen : (e:E) ≠ 0 := by intro hz; simp [hz] at he
    have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs hen bS bE
    exact (tubeMeasureDensity_angular bS bE (tube_dimension_eq bS bE L) he
      hpos.2.2 hpos.1.det_pos hpos.2.1).symm
  have hh := affineEpigraph_angular_f_weighted_drift hΩ hcv hu hp a L hD hK hzero hs bS bE
  dsimp only at hh
  dsimp only [H] at hw
  simpa only [hw] using hh

end AffineBernstein
end

end OAI
