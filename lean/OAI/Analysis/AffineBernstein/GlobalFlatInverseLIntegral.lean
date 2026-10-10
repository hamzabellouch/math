import Mathlib
import OAI.Analysis.AffineBernstein.ActualFlatInverse
import OAI.Analysis.AffineBernstein.GlobalFlatAreaLIntegral

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

/- Global exact inverse-second-form area transport on the entire literal flat support chart.
All metric and parametrization data are derived from the original strictly
convex graph. Neither stationarity nor a measure-transport law is assumed. -/
theorem affineEpigraph_flat_chart_global_inverseArea_lintegral {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (e : Fin n ≃ ι ⊕ κ) (hJe : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    (ℓ : S →L[ℝ] ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let X := fun x : Space n => supportParam Y (q₀+J x)
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.prod bE.toBasis).reindex eA.symm
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
      φ.source = {x | (q₀+J x).1 ∈ B} ∧ φ.target ⊆ Ω ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      (∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x))) ∧
      ∀ (K : Set (Space n)), MeasurableSet K → K ⊆ φ.source →
      (∫⁻ x in K, ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (q₀+J x) bS)
        (tubeRadiusMatrix H (q₀+J x) bE) (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))) * ENNReal.ofReal
        (‖supportConormal H (q₀+J x)‖ *
          inverseMatrixPair (tubeBaseMatrix H (q₀+J x) bS) (fun i => ℓ (bS i)) (fun i => ℓ (bS i)))) =
        ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
          ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * ENNReal.ofReal
            (‖(graphConormalAt u y).comp L.toContinuousLinearMap‖ *
              inverseMatrixPair (hessian u y)
                (fun i => dirDeriv (coordinateVector n i) (pulledBaseGraphFunction u a L ℓ) y)
                (fun i => dirDeriv (coordinateVector n i) (pulledBaseGraphFunction u a L ℓ) y)) := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let X := fun x : Space n => supportParam Y (q₀+J x)
  obtain ⟨φ,hsource,ht,hφ,hψ,heφ,harea⟩ := affineEpigraph_flat_chart_global_area_lintegral
    hΩ hcv hu hp a L hB hK hzero q₀ bS bE hd J hi hJ e hJe
  change ∃ φ, _
  refine ⟨φ,hsource,ht,hφ,hψ,heφ,?_⟩
  intro K hKc hKW
  let w : Space n → ℝ := fun y => ‖(graphConormalAt u y).comp L.toContinuousLinearMap‖ *
    inverseMatrixPair (hessian u y)
      (fun i => dirDeriv (coordinateVector n i) (pulledBaseGraphFunction u a L ℓ) y)
      (fun i => dirDeriv (coordinateVector n i) (pulledBaseGraphFunction u a L ℓ) y)
  rw [← harea K hKc hKW (fun y => ENNReal.ofReal (w y))]
  apply setLIntegral_congr_fun hKc
  intro x hx
  have hq : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by simp [inner_add_left,hd,hJ]
  have hs : (q₀+J x).1 ∈ B := by
    have hh := hKW hx
    rwa [hsource] at hh
  have hchart : (fun y => a+L (supportParam Y (q₀+J y))) =ᶠ[nhds x]
      (fun y => (φ y,u (φ y))) := by
    filter_upwards [φ.open_source.mem_nhds (hKW hx)] with y hy
    exact heφ y hy
  have hmetric := affineEpigraph_flat_inverseMetric_transport hΩ hcv hu hp a L hB hK hzero
    q₀ J bS bE e hJe (hφ.contDiffAt (φ.open_source.mem_nhds (hKW hx)))
    (smooth_chart_jacobian_ne φ hφ hψ (hKW hx)) hs
    (by rw [hq]; norm_num) hchart ℓ
  change ‖supportConormal H (q₀+J x)‖ *
    inverseMatrixPair (tubeBaseMatrix H (q₀+J x) bS) (fun i => ℓ (bS i)) (fun i => ℓ (bS i)) =
      w (φ x) at hmetric
  change _ * ENNReal.ofReal _ = _ * ENNReal.ofReal (w (φ x))
  rw [hmetric]

end AffineBernstein
end

end OAI
