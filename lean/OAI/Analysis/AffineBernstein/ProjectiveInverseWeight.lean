import Mathlib
import OAI.Analysis.AffineBernstein.ParametricInverseMetric
import OAI.Analysis.AffineBernstein.NewtonBasis

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma homogeneous_fiber_fderiv_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (v : S × E) :
    fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2)
      (s,c • e) (normalScale c v) =
    c * fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) v := by
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have he : (fun q => H (normalScale c q)) =ᶠ[𝓝 (s,e)] (fun q => c * H q) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hD.mem_nhds hs)] with q hq
    exact homogeneousSupport_smul (hK _ hq) (hne _ hq) q.2 hc
  have hl : fderiv ℝ (fun q => H (normalScale c q)) (s,e) =
      (fderiv ℝ H (s,c • e)).comp (normalScale c) := by
    exact (hHc.hasFDerivAt.comp (s,e) (normalScale c).hasFDerivAt).fderiv
  have hr := fderiv_const_mul hH c
  have hh := congrArg (fun A : (S × E) →L[ℝ] ℝ => A v) he.fderiv_eq
  rw [hl,hr] at hh
  exact hh

lemma homogeneous_supportConormal_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e)) :
    supportConormal (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) =
      c • supportConormal (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) := by
  apply ContinuousLinearMap.ext
  intro v
  have hh := homogeneous_fiber_fderiv_scale hD hs hK hne hc hH hHc (v.1,0)
  simp only [normalScale_apply,smul_zero] at hh
  change fderiv ℝ _ (s,c • e) (v.1,0) - inner ℝ (c • e) v.2 =
    c * (fderiv ℝ _ (s,e) (v.1,0) - inner ℝ e v.2)
  rw [hh,real_inner_smul_left]
  ring

/- The conormal norm exactly cancels inverse-B homogeneity. Thus this is a
well-defined weight on rays, not a coordinate-dependent flat-chart weight. -/
lemma homogeneous_inverseMetricWeight_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (bS : Module.Basis ι ℝ S)
    (hB : (tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) bS).det ≠ 0)
    (v w : ι → ℝ) :
    let H := fun q : S × E => homogeneousSupport (K q.1) q.2
    ‖supportConormal H (s,c • e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,c • e) bS) v w =
      ‖supportConormal H (s,e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,e) bS) v w := by
  let : NormSMulClass ℝ ((S × E) →L[ℝ] ℝ) :=
    NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := ((S × E) →L[ℝ] ℝ))
  dsimp only
  rw [homogeneous_supportConormal_scale hD hs hK hne hc
    (hH.differentiableAt (by simp)) (hHc.differentiableAt (by simp)),
    homogeneous_tubeBaseMatrix_scale hD hs hK hne hc hH hHc,
    inverseMatrixPair_smul_matrix _ hB c hc.ne',norm_smul,Real.norm_of_nonneg hc.le]
  field_simp

end AffineBernstein
end

end OAI
