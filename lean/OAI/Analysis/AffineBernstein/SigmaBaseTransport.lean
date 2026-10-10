import Mathlib
import OAI.Analysis.AffineBernstein.SigmaTransform

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section SigmaBaseTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuousAt_tubeLogMassWeight {k : ℕ} {H : Space k × E → ℝ}
    {q : Space k × E} (hH : ContDiffAt ℝ ∞ H q)
    (hs : ∀ i, q.1 i ≠ 0)
    (hd : (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0) :
    ContinuousAt (tubeLogMassWeight H) q := by
  let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hM := contDiffAt_tubeBaseMatrix hH bS
  have hi (i : Fin k) : ContinuousAt (fun z => (tubeBaseMatrix H z bS)⁻¹ i i) q := by
    simp only [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv]
    exact ((((continuousDetRows (ι:=Fin k)).contDiff.contDiffAt.comp _ hM).continuousAt.inv₀ hd).mul
      (contDiffAt_adjugate_entries hM i i).continuousAt)
  have hcoord (i : Fin k) : ContinuousAt (fun z : Space k × E => z.1 i) q := by fun_prop
  have hc : ContinuousAt (fun z => 1 + ∑ i, H z*(tubeBaseMatrix H z bS)⁻¹ i i/(z.1 i)^2) q := by
    apply continuousAt_const.add
    apply tendsto_finsetSum
    intro i _
    exact (hH.continuousAt.mul (hi i)).div ((hcoord i).pow 2) (pow_ne_zero _ (hs i))
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ z in 𝓝 q, ∀ i, z.1 i ≠ 0 :=
    Filter.eventually_all.mpr (fun i => (hcoord i).eventually_ne (hs i))
  filter_upwards [he] with z hz
  exact tubeLogMassWeight_eq H z hz

omit [CompleteSpace E] in
lemma aemeasurable_tube_sigma {n k d : ℕ} (H : Space k × E → ℝ)
    (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ E)
    {Q : Set (Space k)} (hQ : MeasurableSet Q)
    (hbase : ∀ s ∈ Q, ∀ i, s i ≠ 0)
    (hH : ∀ s ∈ Q, ∀ e : E, e ≠ 0 → ContDiffAt ℝ ∞ H (s,e))
    (hp : ∀ s ∈ Q, ∀ e : E, e ≠ 0 → 0 < H (s,e) ∧
      (tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0) :
    AEMeasurable (fun q : Space k × Metric.sphere (0:E) 1 =>
      ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
        (q.1,q.2)*tubeLogMassWeight H (q.1,q.2)))
      ((volume.restrict Q).prod (volume : Measure E).toSphere) := by
  rw [Measure.restrict_prod_eq_prod_univ]
  apply ContinuousOn.aemeasurable _ (hQ.prod MeasurableSet.univ)
  intro q hq
  have he : (q.2:E) ≠ 0 := Metric.ne_of_mem_sphere q.2.property one_ne_zero
  have hm : Continuous (fun q : Space k × Metric.sphere (0:E) 1 => (q.1,(q.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hpcont : ContinuousAt (fun z : Space k × E =>
      tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE z *
        tubeLogMassWeight H z) (q.1,(q.2:E)) :=
    (continuousAt_tubeMeasureDensity (hH q.1 hq.1 _ he) _ bE
      (hp q.1 hq.1 _ he).1).mul
        (continuousAt_tubeLogMassWeight (hH q.1 hq.1 _ he) (hbase q.1 hq.1)
          (hp q.1 hq.1 _ he).2)
  exact (ENNReal.continuous_ofReal.continuousAt.comp
    (ContinuousAt.comp (f:=fun z : Space k × Metric.sphere (0:E) 1 => (z.1,(z.2:E)))
      (g:=fun z : Space k × E => tubeMeasureDensity n H
        (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE z * tubeLogMassWeight H z)
      hpcont hm.continuousAt)).continuousWithinAt


/- Full base-and-normal covariance of actual sigma: positive diagonal base
normalization and an arbitrary transverse GL change preserve its cell mass.
The assumptions describe local regularity and convexity of the support function,
not an integral bound or a transport law. -/
lemma sigma_cell_linear_comp {k d : ℕ}
    (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ E)
    (B : Space k ≃L[ℝ] Space k) (A : E ≃L[ℝ] E)
    (a : Fin k → ℝ) (ha : ∀ i, a i ≠ 0) (hBa : ∀ s i, B s i = a i*s i)
    {K : Space k → Set E} {D : Set (Space k)} (hD : IsOpen D)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : B '' Q ⊆ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    (hs : ∀ s ∈ Q, ∀ i, s i ≠ 0)
    (hH : ∀ s ∈ D, ∀ e : E, e ≠ 0 → ContDiffAt ℝ ∞
      (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hr : ∀ s ∈ D, ∀ e : E, e ≠ 0 → ∀ v : E, fderiv ℝ
      (fderiv ℝ (fun q : Space k × E => homogeneousSupport (K q.1) q.2)) (s,e) (0,v) (0,e) = 0)
    (hp : ∀ s ∈ D, ∀ e : E, e ≠ 0 → 0 < homogeneousSupport (K s) e ∧
      0 < (tubeBaseMatrix (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e)
        (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ∧
      0 < tubeAngularDensity (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e) bE) :
    let H := fun q : Space k × E => homogeneousSupport (K q.1) q.2
    let H' := fun q : Space k × E => H (B q.1,A q.2)
    let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ q : Space k × Metric.sphere (0:E) 1,
      ENNReal.ofReal (tubeMeasureDensity (k+d) H' bS bE (q.1,q.2)*tubeLogMassWeight H' (q.1,q.2))
      ∂(volume.restrict Q).prod (volume : Measure E).toSphere) =
    (∫⁻ q : Space k × Metric.sphere (0:E) 1,
      ENNReal.ofReal (tubeMeasureDensity (k+d) H bS bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
      ∂(volume.restrict (B '' Q)).prod (volume : Measure E).toSphere) := by
  let H := fun q : Space k × E => homogeneousSupport (K q.1) q.2
  let H' := fun q : Space k × E => H (B q.1,A q.2)
  let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let f : Space k × Metric.sphere (0:E) 1 → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (tubeMeasureDensity (k+d) H bS bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
  let f' : Space k × Metric.sphere (0:E) 1 → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (tubeMeasureDensity (k+d) H' bS bE (q.1,q.2)*tubeLogMassWeight H' (q.1,q.2))
  have hBs (s : Space k) (hsQ : s ∈ Q) : B s ∈ D := hQD ⟨s,hsQ,rfl⟩
  have heA (e : E) (he : e ≠ 0) : A e ≠ 0 := fun h => he (A.injective (by simpa using h))
  have hh' (s : Space k) (hsQ : s ∈ Q) (e : E) (he : e ≠ 0) : ContDiffAt ℝ ∞ H' (s,e) := by
    have hh : ContDiffAt ℝ ∞ H (B s,A e) := hH _ (hBs s hsQ) _ (heA e he)
    have hm : ContDiffAt ℝ ∞ (fun q : Space k × E => (B q.1,A q.2)) (s,e) :=
      (B.contDiff.contDiffAt.comp _ contDiffAt_fst).prodMk (A.contDiff.contDiffAt.comp _ contDiffAt_snd)
    exact ContDiffAt.comp (f:=fun q : Space k × E => (B q.1,A q.2)) (g:=H) (s,e) hh hm
  have hp' (s : Space k) (hsQ : s ∈ Q) (e : E) (he : e ≠ 0) :
      0 < H' (s,e) ∧ (tubeBaseMatrix H' (s,e) bS).det ≠ 0 := by
    refine ⟨(hp _ (hBs s hsQ) _ (heA e he)).1,?_⟩
    have hm := tubeBaseMatrix_linear_comp B.toContinuousLinearMap A.toContinuousLinearMap
      (H:=H) (q:=(s,e)) (hH _ (hBs s hsQ) _ (heA e he)) bS
    change (tubeBaseMatrix (fun z => H (B.toContinuousLinearMap z.1,A.toContinuousLinearMap z.2)) (s,e) bS).det ≠ 0
    rw [hm,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,LinearMap.det_toMatrix]
    exact mul_ne_zero (mul_ne_zero B.toLinearEquiv.isUnit_det'.ne_zero
      (hp _ (hBs s hsQ) _ (heA e he)).2.1.ne') B.toLinearEquiv.isUnit_det'.ne_zero
  have hf' : AEMeasurable f' ((volume.restrict Q).prod (volume : Measure E).toSphere) :=
    aemeasurable_tube_sigma H' bE hQ hs hh' hp'
  have hBQ : MeasurableSet (B '' Q) := B.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hQ
  have hf : AEMeasurable f ((volume.restrict (B '' Q)).prod (volume : Measure E).toSphere) :=
    aemeasurable_tube_sigma H bE hBQ
      (by rintro _ ⟨s,hsQ,rfl⟩ i; rw [hBa]; exact mul_ne_zero (ha i) (hs s hsQ i))
      (fun s hsQ => hH s (hQD hsQ))
      (fun s hsQ e he => ⟨(hp s (hQD hsQ) e he).1,(hp s (hQD hsQ) e he).2.1.ne'⟩)
  change (∫⁻ q, f' q ∂(volume.restrict Q).prod (volume : Measure E).toSphere) =
    ∫⁻ q, f q ∂(volume.restrict (B '' Q)).prod (volume : Measure E).toSphere
  rw [lintegral_prod f' hf',lintegral_prod f hf]
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ:=volume) hQ
    (fun _ _ => B.hasFDerivAt.hasFDerivWithinAt) B.injective.injOn
    (fun s => ∫⁻ e, f (s,e) ∂(volume : Measure E).toSphere)
  rw [hj]
  apply setLIntegral_congr_fun hQ
  intro s hsQ
  exact sphere_sigma_density_linear_comp bE B A a ha hBa hD (hBs s hsQ) hK hne (hs s hsQ)
    (hH _ (hBs s hsQ)) (hr _ (hBs s hsQ)) (hp _ (hBs s hsQ))
end SigmaBaseTransport



end DependencyScope
end AffineBernstein
end

end OAI
