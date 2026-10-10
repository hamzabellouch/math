import Mathlib
import OAI.Analysis.AffineBernstein.FlatTubePositive
import OAI.Analysis.AffineBernstein.FlatInverseMetric
import OAI.Analysis.AffineBernstein.ActualConormalScale

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def pulledBaseGraphFunction {n : ℕ} (u : Space n → ℝ) (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (ℓ : S →L[ℝ] ℝ) (x : Space n) : ℝ :=
  ℓ (L.symm ((x,u x)-a)).1

omit [CompleteSpace S] [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma contDiffAt_pulledBaseGraphFunction {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (ℓ : S →L[ℝ] ℝ) :
    ContDiffAt ℝ ∞ (pulledBaseGraphFunction u a L ℓ) x :=
  ℓ.contDiff.contDiffAt.comp x
    ((L.symm.contDiff.contDiffAt.comp x ((contDiffAt_id.prodMk hu).sub contDiffAt_const)).fst)

/- Actual pointwise inverse-B identity in every smooth flat support chart.
The conormal normalization is derived from the original graph and support
Gauss equations. There is no assumed inverse-metric or stationarity law. -/
theorem affineEpigraph_flat_inverseMetric_transport {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (J : Space n →L[ℝ] (S × E))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ) (hJe : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    {φ : Space n → Space n} {x : Space n} (hφ : ContDiffAt ℝ ∞ φ x)
    (hJφ : (parametricJacobian φ x).det ≠ 0) (hx : (q₀+J x).1 ∈ B)
    (hd : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) ≠ 0)
    (hchart : (fun y => a+L (supportParam
      (fun q : S × E => gaussPoint {z | (q.1,z) ∈ affineEpigraphPullback Ω u a L} q.2)
        (q₀+J y))) =ᶠ[nhds x] (fun y => (φ y,u (φ y))))
    (ℓ : S →L[ℝ] ℝ) :
    let H := fun q : S × E => homogeneousSupport {z | (q.1,z) ∈ affineEpigraphPullback Ω u a L} q.2
    let f := pulledBaseGraphFunction u a L ℓ
    ‖supportConormal H (q₀+J x)‖ *
      inverseMatrixPair (tubeBaseMatrix H (q₀+J x) bS) (fun i => ℓ (bS i)) (fun i => ℓ (bS i)) =
    ‖(graphConormalAt u (φ x)).comp L.toContinuousLinearMap‖ *
      inverseMatrixPair (hessian u (φ x))
        (fun i => dirDeriv (coordinateVector n i) f (φ x))
        (fun i => dirDeriv (coordinateVector n i) f (φ x)) := by
  let H := fun q : S × E => homogeneousSupport {z | (q.1,z) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {z | (q.1,z) ∈ affineEpigraphPullback Ω u a L} q.2
  let X := fun y : Space n => supportParam Y (q₀+J y)
  let f := pulledBaseGraphFunction u a L ℓ
  have he : (q₀+J x).2 ≠ 0 := by intro hz; exact hd (by simp [hz])
  obtain ⟨hb,_,_⟩ := affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hx he
  have hcx := congrArg Prod.fst hchart.self_of_nhds
  change (a+L (X x)).1 = φ x at hcx
  have hxΩ : φ x ∈ Ω := by
    change (a+L (X x)).1 ∈ Ω at hb
    rwa [hcx] at hb
  have huc := hu.contDiffAt (hΩ.mem_nhds hxΩ)
  obtain ⟨c,hc,hν⟩ := affineEpigraph_supportConormal_scale hΩ hcv hu hp a L hB hK hzero hx he
  change supportConormal H (q₀+J x) =
    c • (graphConormalAt u (a+L (X x)).1).comp L.toContinuousLinearMap at hν
  rw [hcx] at hν
  have hf := (contDiffAt_pulledBaseGraphFunction huc a L ℓ).differentiableAt (by simp)
  have hh := graph_chart_inverseMetric_transport huc hφ (hp _ hxΩ).det_pos.ne' hJφ
    hf L a hchart c hc
  change ‖c • (graphConormalAt u (φ x)).comp L.toContinuousLinearMap‖ *
    parametricInverseMetric X (c • (graphConormalAt u (φ x)).comp L.toContinuousLinearMap)
      (f ∘ φ) x = _ at hh
  rw [← hν] at hh
  have heq : f ∘ φ =ᶠ[nhds x] (fun y => ℓ (q₀+J y).1) := by
    filter_upwards [hchart] with y hy
    change a+L (X y) = (φ y,u (φ y)) at hy
    change ℓ (L.symm ((φ y,u (φ y))-a)).1 = _
    rw [← hy]
    simp [X,supportParam]
  have hmetric : parametricInverseMetric X (supportConormal H (q₀+J x)) (f ∘ φ) x =
      inverseMatrixPair (tubeBaseMatrix H (q₀+J x) bS) (fun i => ℓ (bS i)) (fun i => ℓ (bS i)) := by
    have hdv : (fun i => dirDeriv (coordinateVector n i) (f ∘ φ) x) =
        (fun i => dirDeriv (coordinateVector n i) (fun y => ℓ (q₀+J y).1) x) := by
      funext i
      unfold dirDeriv
      rw [heq.fderiv_eq (𝕜 := ℝ)]
    unfold parametricInverseMetric
    rw [hdv]
    change parametricInverseMetric _ _ (fun y => ℓ (q₀+J y).1) x = _
    obtain ⟨hHs,hYs,heul,hgrad⟩ := affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero hx he
    obtain ⟨hBp,hRp⟩ := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hB hK hzero hx bS bE hd
    exact parametricInverseMetric_flat_base q₀ J hHs hYs heul hgrad bS bE e hJe
      hBp.det_pos.ne' hRp.det_pos.ne' ℓ
  rw [hmetric] at hh
  exact hh

end AffineBernstein
end

end OAI
