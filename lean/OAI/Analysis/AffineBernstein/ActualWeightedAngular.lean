import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeMetricPositivity

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

omit [MeasurableSpace E] [BorelSpace E] in
lemma affineEpigraph_tube_angular_smooth {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE δ
    ContDiffOn ℝ ∞ (fun e => H (s,e)) {e | e ≠ 0} ∧
    ContDiffOn ℝ ∞ (fun e => P (s,e)) {e | e ≠ 0} ∧
    ContDiffOn ℝ ∞ (fun e => F (s,e)) {e | e ≠ 0} ∧
    (∀ e ∈ {e : E | e ≠ 0}, ∀ v, fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v e = 0) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hH (e : E) (he : e ≠ 0) : ContDiffAt ℝ ∞ H (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  refine ⟨?_,?_,?_,?_⟩
  · intro e he
    exact ((hH e he).comp e (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · intro e he
    have hp' := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he bS bE
    exact (((hH e he).log hp'.2.2.ne').comp e (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · intro e he
    exact ((affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hs he bS bE δ).comp e
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · intro e he v
    rw [second_fderiv_prod_right (hH e he)]
    exact affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hs he v

/- The actual angular weighted drift integrates to exactly `-n/2` times
its nonnegative angular energy. No angular PDE or integration formula is assumed. -/
theorem affineEpigraph_angular_f_weighted_drift {n : ℕ} {Ω : Set (Space n)}
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
    let W := fun e => Real.exp (2*P (s,e)+(((n : ℝ)+2)/2)*F (s,e))
    (∫ e : sphere (0:E) 1, W e*roundHessianContraction bE N (fun y => F (s,y)) e ∂volume.toSphere) +
    2*(∫ e : sphere (0:E) 1, W e*N e (dP e) (dF e) ∂volume.toSphere) +
    (∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) =
    (-(n : ℝ)/2)*(∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) := by
  dsimp only
  have hsmooth := affineEpigraph_tube_angular_smooth hΩ hcv hu hp a L hD hK hzero hs bS bE
    (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  have hU : IsOpen {e : E | e ≠ 0} := isClosed_singleton.isOpen_compl
  have hSU : sphere (0:E) 1 ⊆ {e : E | e ≠ 0} := by
    intro e he
    have hen : ‖e‖ = 1 := mem_sphere_zero_iff_norm.1 he
    intro hz
    simp [hz] at hen
  have hh := integral_supportNewtonTensor_weighted_drift bE hU hSU
    hsmooth.1 hsmooth.2.2.2 hsmooth.2.1 hsmooth.2.2.1 2 (((n : ℝ)+2)/2)
  convert hh using 1
  ring

end AffineBernstein
end

end OAI
