import Mathlib
import OAI.Analysis.AffineBernstein.DensityTransform
import OAI.Analysis.AffineBernstein.WeightTransform
import OAI.Analysis.AffineBernstein.HomogeneousSphere

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section SigmaTransform
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuousAt_tubeLogMassWeight_fixed {k : ℕ} {H : Space k × E → ℝ}
    {s : Space k} {e : E} (hH : ContDiffAt ℝ ∞ H (s,e))
    (hs : ∀ i, s i ≠ 0)
    (hd : (tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0) :
    ContinuousAt (fun y => tubeLogMassWeight H (s,y)) e := by
  simp_rw [tubeLogMassWeight_eq H (s,_) hs]
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro i _
  have hM := contDiffAt_tubeBaseMatrix hH (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hi : ContinuousAt (fun q => (tubeBaseMatrix H q
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i) (s,e) := by
    simp only [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv]
    exact ((((continuousDetRows (ι:=Fin k)).contDiff.contDiffAt.comp _ hM).continuousAt.inv₀ hd).mul
      (contDiffAt_adjugate_entries hM i i).continuousAt)
  exact ((hH.continuousAt.mul hi).comp (continuousAt_const.prodMk continuousAt_id)).div_const _

/- Exact covariance of the actual weighted density integrated over all normal
directions, with its transverse GL Jacobian cancelled by the sphere measure. -/
lemma sphere_sigma_density_linear_comp {k d : ℕ}
    (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ E)
    (B : Space k ≃L[ℝ] Space k) (A : E ≃L[ℝ] E)
    (a : Fin k → ℝ) (ha : ∀ i, a i ≠ 0) (hBa : ∀ s i, B s i = a i*s i)
    {K : Space k → Set E} {D : Set (Space k)} (hD : IsOpen D) {s : Space k} (hsD : B s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    (hs : ∀ i, s i ≠ 0)
    (hH : ∀ e : E, e ≠ 0 → ContDiffAt ℝ ∞
      (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (B s,e))
    (hr : ∀ e : E, e ≠ 0 → ∀ v : E, fderiv ℝ
      (fderiv ℝ (fun q : Space k × E => homogeneousSupport (K q.1) q.2)) (B s,e) (0,v) (0,e) = 0)
    (hp : ∀ e : E, e ≠ 0 → 0 < homogeneousSupport (K (B s)) e ∧
      0 < (tubeBaseMatrix (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (B s,e)
        (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ∧
      0 < tubeAngularDensity (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (B s,e) bE) :
    let H := fun q : Space k × E => homogeneousSupport (K q.1) q.2
    let H' := fun q : Space k × E => H (B q.1,A q.2)
    let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ e : Metric.sphere (0:E) 1,
      ENNReal.ofReal (tubeMeasureDensity (k+d) H' bS bE (s,e)*tubeLogMassWeight H' (s,e))
      ∂(volume : Measure E).toSphere) =
    ENNReal.ofReal |B.toLinearMap.det| * ∫⁻ e : Metric.sphere (0:E) 1,
      ENNReal.ofReal (tubeMeasureDensity (k+d) H bS bE (B s,e)*tubeLogMassWeight H (B s,e))
      ∂(volume : Measure E).toSphere := by
  let H := fun q : Space k × E => homogeneousSupport (K q.1) q.2
  let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let f : E → ℝ≥0∞ := fun e =>
    ENNReal.ofReal (tubeMeasureDensity (k+d) H bS bE (B s,e)*tubeLogMassWeight H (B s,e))
  have hdE : Module.finrank ℝ E = d+1 := by
    simpa using Module.finrank_eq_card_basis bE.toBasis
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have hBs (i : Fin k) : B s i ≠ 0 := by rw [hBa]; exact mul_ne_zero (ha i) (hs i)
  have hf : Measurable f := by
    apply ContinuousOn.measurable_of_countable_compl (s:=({0}:Set E)ᶜ)
    · intro e he
      have h0 : e ≠ 0 := he
      apply ContinuousAt.continuousWithinAt
      apply ENNReal.continuous_ofReal.continuousAt.comp
      exact ((continuousAt_tubeMeasureDensity (hH e h0) bS bE (hp e h0).1).comp
        (continuousAt_const.prodMk continuousAt_id)).mul
        (continuousAt_tubeLogMassWeight_fixed (hH e h0) hBs (hp e h0).2.1.ne')
    · simp only [compl_compl]; exact countable_singleton 0
  have hscale (e : E) (he : e ≠ 0) (r : ℝ) (hr0 : 0 < r) :
      f (r • e) = ENNReal.ofReal (r⁻¹ ^ (Module.finrank ℝ E-1))*f e := by
    have hre : r • e ≠ 0 := smul_ne_zero hr0.ne' he
    have hμ := homogeneous_tubeMeasureDensity_scale hD hsD hK hne hr0 (hH e he) (hH _ hre)
      bS bE (hp e he).1 (hp e he).2.1 (hp e he).2.2
    simp only [Fintype.card_fin] at hμ
    dsimp only [f]
    rw [hμ,tubeLogMassWeight_homogeneous hD hsD hK hne hr0 (hH e he) (hH _ hre)
      hBs (hp e he).2.1.ne',hdE,Nat.add_sub_cancel_right,mul_assoc,
      ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hr0.le) _)]
  have htrans := sphere_lintegral_homogeneous_linear (volume : Measure E) A f hf hscale
  dsimp only
  rw [htrans,← mul_assoc,← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro e
  have he : (e:E) ≠ 0 := Metric.ne_of_mem_sphere e.property one_ne_zero
  have hae : A e ≠ 0 := fun h => he (A.injective (by simpa using h))
  have hen : ‖(e:E)‖ = 1 := by simp
  change ENNReal.ofReal (tubeMeasureDensity (k+d) (fun z => H (B.toContinuousLinearMap z.1,A z.2)) bS bE (s,(e:E)) *
    tubeLogMassWeight (fun z => H (B.toContinuousLinearMap z.1,A z.2)) (s,(e:E))) = _
  rw [tubeMeasureDensity_linear_comp (n:=k+d) B.toContinuousLinearMap A
      (H:=H) (q:=(s,(e:E))) (hH _ hae) bS bE hen (hr _ hae)]
  have hw : tubeLogMassWeight (fun z => H (B.toContinuousLinearMap z.1,A z.2)) (s,(e:E)) =
      tubeLogMassWeight H (B s,A e) :=
    tubeLogMassWeight_diagonal_comp B.toContinuousLinearMap A.toContinuousLinearMap a ha hBa
      (H:=H) (q:=(s,(e:E))) (hH _ hae) hs
  rw [hw]
  change ENNReal.ofReal ((|B.toLinearMap.det| * |A.toLinearMap.det| / ‖A e‖) *
    tubeMeasureDensity (k+d) H bS bE (B s,A e) * tubeLogMassWeight H (B s,A e)) = _
  rw [mul_assoc,ENNReal.ofReal_mul (by positivity :
    0 ≤ |B.toLinearMap.det| * |A.toLinearMap.det| / ‖A e‖)]
  dsimp only [f]
  rw [div_eq_mul_inv,ENNReal.ofReal_mul (by positivity :
    0 ≤ |B.toLinearMap.det| * |A.toLinearMap.det|),ENNReal.ofReal_mul (abs_nonneg _)]
  ring
end SigmaTransform



end DependencyScope
end AffineBernstein
end

end OAI
