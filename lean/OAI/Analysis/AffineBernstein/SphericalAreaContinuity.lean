import Mathlib
import OAI.Analysis.AffineBernstein.FlatProductCoordinates
import OAI.Analysis.AffineBernstein.WholeSphereProjective
import OAI.Analysis.AffineBernstein.ActualProjectiveAreaChart

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SphericalAreaContinuity
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [CompleteSpace E] in
lemma continuousAt_sphericalArea {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ)
    (hB : 0 < (tubeBaseMatrix H q bS).det) (hQ : 0 < tubeAngularDensity H q bE) :
    ContinuousAt (fun y => Real.rpow (tubeBaseMatrix H y bS).det δ *
        Real.rpow (tubeAngularDensity H y bE) (1-δ)) q := by
  have hb := (contDiffAt_tubeBaseMatrix hH bS).continuousAt
  have hq := (contDiffAt_tubeAngularDensity hH bE).continuousAt
  have hd := continuous_id.matrix_det.continuousAt.comp hb
  exact (hd.rpow_const (Or.inl hB.ne')).mul (hq.rpow_const (Or.inl hQ.ne'))
end SphericalAreaContinuity

section WholeSphereArea
open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The actual full-sphere affine area is the sum of the two actual flat chart areas.
Both flat charts are complete; their omitted equator has actual sphere measure zero. -/
theorem affineEpigraph_sphere_area_two_flat_lintegral {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) (bS : Module.Basis ι ℝ S)
    (bF : OrthonormalBasis κ ℝ F) (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E)  :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    let flatEnergy := fun h : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E => fun x : F =>
      ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) bS)
        (tubeRadiusMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) (flatProductFiberBasis bF h)) δ)
    (∫⁻ e : Metric.sphere (0:E) 1, ENNReal.ofReal
      (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
        Real.rpow (tubeAngularDensity H (s,e) bRef) (1-δ))
        ∂volume.toSphere) = (∫⁻ x : F, flatEnergy f x) +
      (∫⁻ x : F, flatEnergy (f.trans (LinearIsometryEquiv.neg ℝ)) x) := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
  let g : E → ℝ≥0∞ := fun e => ENNReal.ofReal
    (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
      Real.rpow (tubeAngularDensity H (s,e) bRef) (1-δ))
  have hg : Measurable g := by
    apply ENNReal.measurable_ofReal.comp
    apply measurable_of_continuousOn_compl_singleton (0:E)
    intro e he
    have he0 : e ≠ 0 := by simpa using he
    have hj := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he0).1
    have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he0 bS bRef
    exact ((continuousAt_sphericalArea hj bS bRef δ hpos.1.det_pos hpos.2.1).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  change (∫⁻ e : Metric.sphere (0:E) 1, g e ∂volume.toSphere) = _
  rw [sphere_two_projective_lintegral f g hg]
  congr 1
  · apply lintegral_congr
    intro x
    exact (affineEpigraph_projective_isometry_area_density hΩ hcv hu hp a L hD hK hzero
      hs bS (flatProductFiberBasis bF f) bRef f (flatProductFiberBasis_last bF f) x).symm
  · apply lintegral_congr
    intro x
    exact (affineEpigraph_projective_isometry_area_density hΩ hcv hu hp a L hD hK hzero
      hs bS (flatProductFiberBasis bF (f.trans (LinearIsometryEquiv.neg ℝ))) bRef
      (f.trans (LinearIsometryEquiv.neg ℝ)) (flatProductFiberBasis_last bF _) x).symm

end WholeSphereArea

-- ProductAreaChart

end AffineBernstein
end

end OAI
