import Mathlib
import OAI.Analysis.AffineBernstein.GaussCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

section SupportRadial
open Filter
open scoped Topology
variable {n : ℕ}

lemma continuousAt_hessian {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : ContinuousAt (hessian u) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact ((((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiffAt_const).continuousAt

lemma gaussPoint_pos_smul {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty)
    {x : Space n} {c : ℝ} (hc : 0 < c)
    (hx : DifferentiableAt ℝ (homogeneousSupport K) x)
    (hcx : DifferentiableAt ℝ (homogeneousSupport K) (c • x)) :
    gaussPoint K (c • x) = gaussPoint K x := by
  obtain ⟨hz,heq⟩ := gaussPoint_mem_support hK hne hx
  apply gaussPoint_eq_of_max hK hz _ hcx
  apply homogeneousSupport_eq_of_max hz
  intro y hy
  change inner ℝ (c • x) y ≤ inner ℝ (c • x) (gaussPoint K x)
  simp only [real_inner_smul_left]
  exact mul_le_mul_of_nonneg_left (heq ▸ homogeneousSupport_le hK hy x) hc.le

lemma homogeneousSupport_hessian_smul {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hH : ∀ x : Space n, x ≠ 0 → ContDiffAt ℝ ∞ (homogeneousSupport K) x)
    {x : Space n} (hx : x ≠ 0) {c : ℝ} (hc : 0 < c) :
    hessian (homogeneousSupport K) (c • x) = c⁻¹ • hessian (homogeneousSupport K) x := by
  let H := homogeneousSupport K
  let G := gradient H
  let L : Space n →L[ℝ] Space n := c • ContinuousLinearMap.id ℝ (Space n)
  have hcx : c • x ≠ 0 := smul_ne_zero hc.ne' hx
  have hgc := ((contDiffAt_gradient (hH (c • x) hcx)).differentiableAt (by simp)).hasFDerivAt
  have hj : HasFDerivAt (fun z => G (c • z)) ((fderiv ℝ G (c • x)).comp L) x :=
    hgc.comp x L.hasFDerivAt
  have he : (fun z => G (c • z)) =ᶠ[𝓝 x] G := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz
    exact gaussPoint_pos_smul hK hne hc ((hH z hz).differentiableAt (by simp))
      ((hH (c • z) (smul_ne_zero hc.ne' hz)).differentiableAt (by simp))
  have hder := hj.congr_of_eventuallyEq he.symm
  have hdeq := hder.fderiv
  ext i j
  have hv := congrArg (fun A : Space n →L[ℝ] Space n =>
    inner ℝ (A (coordinateVector n i)) (coordinateVector n j)) hdeq
  simp only [ContinuousLinearMap.comp_apply,L,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,real_inner_smul_left] at hv
  dsimp only [G,H] at hv
  rw [inner_fderiv_gradient (hH x hx),inner_fderiv_gradient (hH (c • x) hcx),
    ← hessian_eq_second (hH x hx),← hessian_eq_second (hH (c • x) hcx)] at hv
  change hessian (homogeneousSupport K) (c • x) i j = c⁻¹ * hessian (homogeneousSupport K) x i j
  rw [hv]
  rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]

lemma support_cofactor_radial_expansion {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hH : ∀ x : Space n, x ≠ 0 → ContDiffAt ℝ ∞ (homogeneousSupport K) x)
    {x : Space n} (hx : x ≠ 0) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ENNReal.ofReal (hessian (homogeneousSupport K) x).adjugate.trace ≤
      ENNReal.ofReal (hessian (homogeneousSupport K) (c • x)).adjugate.trace := by
  rw [homogeneousSupport_hessian_smul hK hne hH hx hc,Matrix.adjugate_smul,Matrix.trace_smul]
  simp only [Fintype.card_fin,smul_eq_mul]
  rw [ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hc.le) _)]
  have hh : (1:ℝ≥0∞) ≤ ENNReal.ofReal (c⁻¹ ^ (n-1)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact one_le_pow₀ ((one_le_inv₀ hc).mpr hc1)
  simpa only [one_mul] using mul_le_mul_left hh
    (ENNReal.ofReal (hessian (homogeneousSupport K) x).adjugate.trace)

end SupportRadial
/- A homogeneous quantity which expands on inward rays has its spherical
integral controlled by its integral over the punctured unit ball. The exact
radial Haar normalization is retained. -/
lemma sphere_lintegral_mul_radial_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞}
    (hf : Measurable (fun e : Metric.sphere (0:E) 1 => f e))
    (hscale : ∀ (e : Metric.sphere (0:E) 1) (r : ℝ), 0 < r → r < 1 → f e ≤ f (r • (e:E))) :
    (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) *
      ENNReal.ofReal (1 / ((Module.finrank ℝ E - 1 + 1 : ℕ):ℝ)) ≤
        ∫⁻ x in Metric.ball (0:E) 1 \ {0}, f x ∂μ := by
  let Φ := homeomorphUnitSphereProd E
  let ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let r₁ : Ioi (0:ℝ) := ⟨1,by change (0:ℝ) < 1; exact one_pos⟩
  let U : Set (Metric.sphere (0:E) 1 × Ioi (0:ℝ)) := univ ×ˢ Iio r₁
  have hU : MeasurableSet U := MeasurableSet.univ.prod measurableSet_Iio
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hprod : (∫⁻ q in U, f q.1 ∂μ.toSphere.prod ν) =
      (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) *
        ENNReal.ofReal (1 / ((Module.finrank ℝ E - 1 + 1 : ℕ):ℝ)) := by
    dsimp only [U]
    rw [setLIntegral_prod (fun q : Metric.sphere (0:E) 1 × Ioi (0:ℝ) => f q.1)
      ((hf.comp measurable_fst).aemeasurable)]
    simp only [lintegral_const,Measure.restrict_apply_univ,Measure.restrict_univ]
    rw [lintegral_mul_const _ hf]
    simp [ν,r₁,Measure.volumeIoiPow_apply_Iio]
  have hsub : Subtype.val '' (Φ ⁻¹' U) = Metric.ball (0:E) 1 \ {0} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,z.property⟩
      rw [Metric.mem_ball,dist_zero_right]
      have hz2 : ((Φ z).2:ℝ) < 1 := hz.2
      simpa [Φ,homeomorphUnitSphereProd_apply_snd_coe] using hz2
    · intro hx
      refine ⟨⟨x,hx.2⟩,?_,rfl⟩
      change True ∧ ((Φ ⟨x,hx.2⟩).2:ℝ) < 1
      exact ⟨trivial,by simpa [Φ,homeomorphUnitSphereProd_apply_snd_coe,
        Metric.mem_ball,dist_zero_right] using hx.1⟩
  have heq : (∫⁻ q in U, f ((Φ.symm q):E) ∂μ.toSphere.prod ν) =
      ∫⁻ x in Metric.ball (0:E) 1 \ {0}, f x ∂μ := by
    rw [← hmp.setLIntegral_comp_preimage_emb Φ.measurableEmbedding
      (fun q => f ((Φ.symm q):E)) U]
    simp only [Φ,Homeomorph.symm_apply_apply]
    rw [setLIntegral_subtype (measurableSet_singleton (0:E)).compl,hsub]
  rw [← hprod,← heq]
  apply setLIntegral_mono' hU
  intro q hq
  have hr : (q.2:ℝ) < 1 := hq.2
  simpa only [Φ,homeomorphUnitSphereProd_symm_apply_coe] using hscale q.1 q.2 q.2.property hr

end AffineBernstein
end

end OAI
