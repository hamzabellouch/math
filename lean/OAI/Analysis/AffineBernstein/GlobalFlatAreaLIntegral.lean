import Mathlib
import OAI.Analysis.AffineBernstein.FlatParametricArea
import OAI.Analysis.AffineBernstein.GlobalGraphChart
import OAI.Analysis.AffineBernstein.FlatChartInjective
import OAI.Analysis.AffineBernstein.WeightedChartLIntegral

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
theorem affineEpigraph_flat_chart_global_area_lintegral {n : ℕ} {Ω : Set (Space n)}
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
    :
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
      ∀ (w : Space n → ℝ≥0∞),
      (∫⁻ x in K, ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (q₀+J x) bS)
        (tubeRadiusMatrix H (q₀+J x) bE) (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))) * w (φ x)) =
        ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
          ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * w y := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let X := fun x : Space n => supportParam Y (q₀+J x)
  let U := {x : Space n | (q₀+J x).1 ∈ B}
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let b := (bS.prod bE.toBasis).reindex eA.symm
  obtain ⟨hU,hLX,him,hiLX⟩ := affineEpigraph_flat_parametrization hΩ hcv hu hp a L hB hK hzero
    q₀ (bE (Sum.inr ())) hd J hi hJ
  have he : (fun x => L.symm ((a+L (X x))-a)) = X := by funext x; simp
  have hX : ContDiffOn ℝ ∞ X U := by
    rw [← he]
    exact L.symm.contDiff.comp_contDiffOn (hLX.sub contDiffOn_const)
  obtain ⟨φ,hsource,ht,heφ₀,hφ,hψ⟩ := exists_smooth_global_graph_chart hU hΩ hLX hu him
    (affineEpigraph_flat_graph_injective hΩ hcv hu hp a L hB hK hzero q₀ (bE (Sum.inr ())) hd J hi hJ) hiLX
  have hs : φ.source ⊆ U := fun x hx => by rwa [hsource] at hx
  have heφ : ∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x)) :=
    fun x hx => heφ₀ x (hs hx)
  change ∃ φ, _
  refine ⟨φ,hsource,ht,hφ,hψ,heφ,?_⟩
  intro K hKc hKW w
  have hq (x : Space n) : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by
    simp [inner_add_left,hd,hJ]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by intro hz; simpa [hz] using hq x
  have hj (x : Space n) (hx : x ∈ U) :=
    affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero hx (hne x)
  have hνx (x : Space n) (hx : x ∈ K) :
      (supportConormal H (q₀+J x)).comp (fderiv ℝ X x) = 0 := by
    obtain ⟨hHs,hYs,heul,hgrad⟩ := hj x (hs (hKW hx))
    have hsp : ContDiffAt ℝ ∞ (supportParam Y) (q₀+J x) := contDiffAt_fst.prodMk hYs
    have hcomp := (hsp.differentiableAt (by simp)).hasFDerivAt.comp x
      (J.hasFDerivAt.const_add q₀)
    have hdX : fderiv ℝ X x = (fderiv ℝ (supportParam Y) (q₀+J x)).comp J := hcomp.fderiv
    rw [hdX]
    ext w
    exact supportConormal_tangent (hHs.differentiableAt (by simp))
      (hYs.differentiableAt (by simp)) heul hgrad.self_of_nhds (J w)
  have hh := graph_chart_weighted_affineArea_lintegral hU hΩ hX hu hp a L φ hs ht hφ hψ heφ
    b hKc hKW (fun x => supportConormal H (q₀+J x))
    (fun _ => (0,-bE (Sum.inr ()))) hνx
    (fun x _ => flat_supportConormal_transverse bE (hq x))
    (fun x hx => affineEpigraph_supportConormal_inward hΩ hcv hu hp a L hB hK hzero
      (hs (hKW hx)) (hne x)) w
  rw [← hh]
  apply setLIntegral_congr_fun hKc
  intro x hx
  apply congrArg (fun r : ℝ => ENNReal.ofReal r * w (φ x))
  obtain ⟨hHs,hYs,heul,hgrad⟩ := hj x (hs (hKW hx))
  change tubeAreaDensity (tubeBaseMatrix H (q₀+J x) bS)
    (tubeRadiusMatrix H (q₀+J x) bE) _ =
    parametricAreaDensity ((bS.prod bE.toBasis).reindex eA.symm)
      (fun y => supportParam Y (q₀+J y)) (supportConormal H (q₀+J x))
      (0,-bE (Sum.inr ())) x
  rw [parametricAreaDensity_flatSupport q₀ J hYs bS bE e hJe]
  obtain ⟨hBp,hRp⟩ := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hB hK hzero
    (e := (q₀+J x).2) (hs (hKW hx)) bS bE (by rw [hq x]; norm_num)
  exact (flatTubeAffineAreaJet_eq hHs hYs heul hgrad bS bE hBp.det_pos hRp.det_pos).symm

end AffineBernstein
end

end OAI
