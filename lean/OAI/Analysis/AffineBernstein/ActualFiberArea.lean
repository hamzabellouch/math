import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeArea
import OAI.Analysis.AffineBernstein.NewtonBasis
import OAI.Analysis.AffineBernstein.FiberArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

section ActualFiberArea
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

omit [CompleteSpace S] in
lemma tubeFullRadiusMatrix_basisFun {m : ℕ} {H : S × Space m → ℝ}
    {s : S} {e : Space m} (hH : ContDiffAt ℝ ∞ H (s,e)) :
    tubeFullRadiusMatrix H (s,e) (EuclideanSpace.basisFun (Fin m) ℝ) =
      hessian (fun y => H (s,y)) e := by
  have hh : ContDiffAt ℝ ∞ (fun y => H (s,y)) e :=
    hH.comp e (contDiffAt_const.prodMk contDiffAt_id)
  ext i j
  simp only [tubeFullRadiusMatrix,Matrix.of_apply]
  rw [hessian_eq_second hh,second_fderiv_prod_right hH]
  simp only [EuclideanSpace.basisFun_apply,coordinateVector]

/- The uniform fiber-area bound is here derived for the literal affine
pullback epigraph of the source solution, not for an abstract tube density.
The endpoint transverse dimension one is included. -/
theorem affineEpigraph_sphere_area_bound {n m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × Space m) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:Space m) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {R : ℝ}
    (hR : ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ R) :
    let H := fun q : S × Space m =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    (∫⁻ e : Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeAngularDensity H (s,e) (EuclideanSpace.basisFun (Fin m) ℝ))
          ∂volume.toSphere) ≤
      (m:ℝ≥0∞)^2 * volume (Metric.closedBall (0:Space m) (R+1)) := by
  let : NeZero m := ⟨by omega⟩
  let K : Set (Space m) := {y | (s,y) ∈ affineEpigraphPullback Ω u a L}
  let H := fun q : S × Space m =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hj (e : Space m) (he : e ≠ 0) : ContDiffAt ℝ ∞ H (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  have hh (e : Space m) (he : e ≠ 0) :
      ContDiffAt ℝ ∞ (homogeneousSupport K) e :=
    (hj e he).comp e (contDiffAt_const.prodMk contDiffAt_id)
  have heq : (fun e : Metric.sphere (0:Space m) 1 =>
      ENNReal.ofReal (tubeAngularDensity H (s,e) (EuclideanSpace.basisFun (Fin m) ℝ))) =
      (fun e : Metric.sphere (0:Space m) 1 =>
        ENNReal.ofReal (hessian (homogeneousSupport K) e).adjugate.trace) := by
    funext e
    rw [tubeAngularDensity,tubeFullRadiusMatrix_basisFun
      (hj e (Metric.ne_of_mem_sphere e.property one_ne_zero))]
  change (∫⁻ e : Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeAngularDensity H (s,e) (EuclideanSpace.basisFun (Fin m) ℝ))
        ∂volume.toSphere) ≤ (m:ℝ≥0∞)^2 * volume (Metric.closedBall (0:Space m) (R+1))
  rw [heq]
  exact sphere_support_cofactor_le_ball hm (hK s hs) ⟨0,interior_subset (hzero s hs)⟩ hh hR

end ActualFiberArea

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Positive-definiteness of the derivative makes a map injective on a convex
set, by strict monotonicity along every segment. -/

/- The actual gradient of a strictly positive-Hessian function is injective;
in particular this applies to every principal-coordinate slice in the source. -/

end AffineBernstein
end

end OAI
