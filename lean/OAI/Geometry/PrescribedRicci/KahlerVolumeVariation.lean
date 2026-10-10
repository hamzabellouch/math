import Mathlib
import OAI.Geometry.PrescribedRicci.CompactParameterIntegral
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy
import OAI.Geometry.PrescribedRicci.KahlerGreenIdentity
import OAI.Geometry.PrescribedPotential.PotentialDensity

namespace OAI

/-! Kahler Volume Variation. -/

section

 

noncomputable section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff ComplexOrder Classical Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma PositivePotential.segment {g : KaehlerMetric A} {φ : SmoothRealFunction A}
    (hp : g.PositivePotential φ) {s : ℝ} (hs : s ∈ Icc 0 1) :
    g.PositivePotential (φ.realSMul s) := by
  intro i z hz
  rw [SmoothRealFunction.hessian_realSMul]
  by_cases h1 : s = 1
  · simpa only [h1, Complex.ofReal_one, one_smul] using hp i z hz
  have hc : (0 : ℂ) < ((1 - s : ℝ) : ℂ) :=
    Complex.pos_iff.mpr ⟨sub_pos.mpr (lt_of_le_of_ne hs.2 h1), rfl⟩
  have hq := (hp i z hz).posSemidef.smul
    (show (0 : ℂ) ≤ (s : ℂ) from Complex.nonneg_iff.mpr ⟨hs.1, rfl⟩)
  have he := ((g.positive i z hz).smul hc).add_posSemidef hq
  convert he using 1
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

lemma continuous_weighted_parameter {E : Type*} [TopologicalSpace E]
    {w : E → ℝ} (hw : Continuous w) {F : ℝ × E → ℝ}
    (hF : ∀ p, p.2 ∈ tsupport w → ContinuousAt F p) :
    Continuous (fun p : ℝ × E => w p.2 * F p) := by
  apply continuous_real_mul_on_tsupport (hw.comp continuous_snd)
  intro p hp
  exact hF p (tsupport_comp_subset_preimage w continuous_snd hp)

lemma chart_det_variation [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (i : Fin A.count)
    {w : X → ℝ} (hw : Continuous w) (hs : tsupport w ⊆ (A.chart i).source) (s : ℝ) :
    HasDerivAt (fun t => ∫ z, localizeFunction i w z *
      (g.matrix i z + t • φ.hessian i z).det.re)
      (∫ z, localizeFunction i w z *
        (fderiv ℝ (fun M : Matrix (Fin d) (Fin d) ℂ => M.det)
          (g.matrix i z + s • φ.hessian i z) (φ.hessian i z)).re) s := by
  obtain ⟨hl, hc, ht⟩ := localizeFunction_continuous_compact i hw hs
  let F (t : ℝ) (z : Coordinates d) := localizeFunction i w z *
    (g.matrix i z + t • φ.hessian i z).det.re
  let F' (t : ℝ) (z : Coordinates d) := localizeFunction i w z *
    (fderiv ℝ (fun M : Matrix (Fin d) (Fin d) ℂ => M.det)
      (g.matrix i z + t • φ.hessian i z) (φ.hessian i z)).re
  have hM (p : ℝ × Coordinates d) (hp : p.2 ∈ tsupport (localizeFunction i w)) :
      ContinuousAt (fun q : ℝ × Coordinates d => g.matrix i q.2 + q.1 • φ.hessian i q.2) p := by
    have hg := ((g.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds (ht hp))).continuousAt
    have hf := ((φ.hessian_smooth i).contDiffAt ((A.chart i).open_target.mem_nhds (ht hp))).continuousAt
    exact (hg.comp continuousAt_snd).add
      (continuousAt_fst.smul (hf.comp continuousAt_snd))
  have hF : Continuous (Function.uncurry F) := by
    apply continuous_weighted_parameter hl
    intro p hp
    exact Complex.continuous_re.continuousAt.comp
      (MongeAmpere.contDiff_det.continuous.continuousAt.comp (hM p hp))
  have hF' : Continuous (Function.uncurry F') := by
    apply continuous_weighted_parameter hl
    intro p hp
    have hf := ((φ.hessian_smooth i).contDiffAt ((A.chart i).open_target.mem_nhds (ht hp))).continuousAt
    exact Complex.continuous_re.continuousAt.comp
      ((((MongeAmpere.contDiff_det.restrict_scalars ℝ).continuous_fderiv (by simp)).continuousAt.comp
        (hM p hp)).clm_apply (hf.comp continuousAt_snd))
  exact KahlerCalculus.hasDerivAt_integral_compact hc hF hF'
    (fun t => (Function.support_mul_subset_left _ _).trans (subset_tsupport _))
    (fun t => (Function.support_mul_subset_left _ _).trans (subset_tsupport _))
    (fun t z => by
      have hh := (hasDerivAt_id t).smul_const (φ.hessian i z) |>.const_add (g.matrix i z)
      have hd := ((MongeAmpere.differentiable_det _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hh
      have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
      convert! hr.const_mul (localizeFunction i w z) using 1
      simp only [F', one_smul, id_eq, Complex.reCLM_apply]
      rfl) s

lemma density_mul_volume (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (g.potentialDensity φ).value ((A.chart i).symm z) * g.volumeCoefficient i z =
      (g.matrix i z + φ.hessian i z).det.re := by
  have he := g.potentialDensity_complex φ i ((A.chart i).mapsTo_symm hz)
  rw [(A.chart i).right_inv hz] at he
  have hn := (g.positive i z hz).det_pos.ne'
  have hh := congrArg (fun c : ℂ => (c * (g.matrix i z).det).re) he
  simp only [volumePolynomial, div_mul_cancel₀ _ hn, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hh
  exact hh

lemma integral_density [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (φ : SmoothRealFunction A) (hp : g.PositivePotential φ) (w : X → ℝ) :
    g.integral (fun x => w x * (g.potentialDensity φ).value x) = (g.deform φ hp).integral w := by
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (A.chart i).open_target.measurableSet
  intro z hz
  change (chartPartition i).value ((A.chart i).symm z) *
      (w ((A.chart i).symm z) * (g.potentialDensity φ).value ((A.chart i).symm z)) *
        g.volumeCoefficient i z = _
  rw [mul_assoc, mul_assoc, density_mul_volume g φ i hz]
  exact (mul_assoc _ _ _).symm

lemma real_smul_hessian (φ : SmoothRealFunction A) (s : ℝ) (i : Fin A.count) (z : Coordinates d) :
    s • φ.hessian i z = (φ.realSMul s).hessian i z := by
  rw [SmoothRealFunction.hessian_realSMul]
  ext j k
  exact Complex.real_smul

lemma integral_density_full [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (φ : SmoothRealFunction A) (w : X → ℝ) :
    g.integral (fun x => w x * (g.potentialDensity φ).value x) =
      ∑ i, ∫ z, localizeFunction i (fun x => (chartPartition i).value x * w x) z *
        (g.matrix i z + φ.hessian i z).det.re := by
  apply Finset.sum_congr rfl
  intro i _
  unfold chartIntegral
  rw [← integral_indicator (A.chart i).open_target.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ (A.chart i).target
  · rw [Set.indicator_of_mem hz]
    simp only [localizeFunction, ite_eq_left hz]
    rw [mul_assoc, mul_assoc, density_mul_volume g φ i hz, ← mul_assoc]
  · simp only [Set.indicator_of_notMem hz, localizeFunction, ite_eq_right hz, zero_mul]

lemma full_firstVariation_eq [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (s : ℝ)
    (hp : g.PositivePotential (φ.realSMul s)) (i : Fin A.count) (w : X → ℝ) :
    (∫ z, localizeFunction i w z *
      (fderiv ℝ (fun M : Matrix (Fin d) (Fin d) ℂ => M.det)
        (g.matrix i z + s • φ.hessian i z) (φ.hessian i z)).re) =
      (g.deform (φ.realSMul s) hp).chartIntegral i
        (fun x => w x * ((g.deform (φ.realSMul s) hp).laplacian φ).value x) := by
  let gs := g.deform (φ.realSMul s) hp
  change _ = ∫ z in (A.chart i).target,
    (w ((A.chart i).symm z) * (gs.laplacian φ).value ((A.chart i).symm z)) * gs.volumeCoefficient i z
  rw [← integral_indicator (A.chart i).open_target.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ (A.chart i).target
  · rw [Set.indicator_of_mem hz]
    simp only [localizeFunction, ite_eq_left hz, real_smul_hessian]
    change w ((A.chart i).symm z) * (fderiv ℝ (fun M : Matrix (Fin d) (Fin d) ℂ => M.det)
      (gs.matrix i z) (φ.hessian i z)).re = _
    rw [MongeAmpere.real_fderiv_det_apply _ _ (isUnit_iff_ne_zero.mpr (gs.positive i z hz).det_pos.ne')]
    have hl := gs.laplacian_localExpression φ i hz
    change (gs.laplacian φ).value ((A.chart i).symm z) = _ at hl
    rw [hl, Complex.mul_re, hermitian_det_im (gs.positive i z hz).isHermitian, zero_mul, sub_zero]
    change _ = (_ * ((gs.matrix i z)⁻¹ * φ.hessian i z).trace.re) * (gs.matrix i z).det.re
    ring
  · simp only [Set.indicator_of_notMem hz, localizeFunction, ite_eq_right hz, zero_mul]

 

theorem volume_firstVariation [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A) (s : ℝ)
    (hp : g.PositivePotential (φ.realSMul s)) :
    HasDerivAt (fun t => g.integral (fun x => ψ.value x *
      (g.potentialDensity (φ.realSMul t)).value x))
      (-(g.deform (φ.realSMul s) hp).integral
        ((g.deform (φ.realSMul s) hp).energy ψ φ).value) s := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => g.chart_det_variation φ i
    ((chartPartition i).continuous.fun_mul ψ.continuous)
    (tsupport_mul_subset_left.trans (chartPartition_support i)) s)
  simp_rw [g.full_firstVariation_eq φ s hp] at hh
  have he : (∑ i, (g.deform (φ.realSMul s) hp).chartIntegral i
      (fun x => ((chartPartition i).value x * ψ.value x) *
        ((g.deform (φ.realSMul s) hp).laplacian φ).value x)) =
      -(g.deform (φ.realSMul s) hp).integral ((g.deform (φ.realSMul s) hp).energy ψ φ).value := by
    rw [← (g.deform (φ.realSMul s) hp).green_identity ψ φ]
    unfold integral
    congr 1
    funext i
    congr 1
    funext x
    ring
  rw [he] at hh
  convert! hh using 1
  funext t
  rw [g.integral_density_full]
  simp only [real_smul_hessian]

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
