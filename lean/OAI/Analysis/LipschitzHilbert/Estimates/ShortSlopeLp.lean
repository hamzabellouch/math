import OAI.Analysis.LipschitzHilbert.Estimates.ShortL2Operator

namespace OAI

/-! The continuous short-time operator agrees on every L2 class with
its integral representative. This permits exact support localization. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def shortSample (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (t : ℝ) (z : ℝ×ℝ) : ℂ :=
  if |t|≤1/4 then f (z.1-t,z.2-t*u z) else 0

theorem shortSample_measurable (u : (ℝ×ℝ) → ℝ) (hu : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hf : Measurable f) :
    Measurable (fun p : ℝ×(ℝ×ℝ) => shortSample u f p.1 p.2) := by
  unfold shortSample
  exact (hf.comp (by fun_prop)).ite (measurableSet_le (by fun_prop) measurable_const) measurable_const

theorem shortSample_energy (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) (t : ℝ) :
    MemLp (shortSample u f t) 2 planeMeasure ∧
      (∫ z, ‖shortSample u f t z‖^2 ∂planeMeasure)≤4*∫ z, ‖f z‖^2 ∂planeMeasure := by
  unfold shortSample
  by_cases ht : |t|≤1/4
  · simpa only [shortSample,ite_eq_left ht,Function.comp_def,verticalSampling,sub_zero] using
      verticalSampling_energy u hu t t 0 ht f hfm hf
  · simp only [ite_eq_right ht,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
    exact ⟨MemLp.zero',by positivity⟩

theorem shortSample_congr_ae (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfg : f=ᵐ[planeMeasure] g) (t : ℝ) :
    shortSample u f t=ᵐ[planeMeasure] shortSample u g t := by
  unfold shortSample
  by_cases ht : |t|≤1/4
  · have hm := verticalSampling_measurable u hu.continuous.measurable t t 0
    have hq : Measure.QuasiMeasurePreserving (verticalSampling u t t 0) planeMeasure planeMeasure :=
      ⟨hm,Measure.absolutelyContinuous_of_le_smul
        (planar_map_le_four _ hm (verticalSampling_antilipschitz u hu t t 0 ht))⟩
    filter_upwards [hq.ae hfg] with z hz
    simpa only [ite_eq_left ht,verticalSampling,sub_zero] using hz
  · simp only [ite_eq_right ht]
    exact Filter.Eventually.of_forall fun _ => rfl

theorem shortSlopeOperator_congr_ae (K : ℝ → ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hfg : f=ᵐ[planeMeasure] g) :
    shortSlopeOperator K u f=ᵐ[planeMeasure] shortSlopeOperator K u g := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), shortSample u f t=ᵐ[planeMeasure] shortSample u g t :=
    Filter.Eventually.of_forall (shortSample_congr_ae u hu f g hfg)
  have hm : MeasurableSet {p : ℝ×(ℝ×ℝ) | shortSample u f p.1 p.2=shortSample u g p.1 p.2} :=
    measurableSet_eq_fun (shortSample_measurable u hu.continuous.measurable f hfm)
      (shortSample_measurable u hu.continuous.measurable g hgm)
  have hs := (Measure.ae_ae_comm hm).mp he
  filter_upwards [hs] with z hz
  have hrep (h : (ℝ×ℝ) → ℂ) : shortSlopeOperator K u h z=∫ t, K t*shortSample u h t z := by
    unfold shortSlopeOperator shortSample
    congr 1
    funext t
    split_ifs <;> simp
  rw [hrep,hrep]
  apply integral_congr_ae
  filter_upwards [hz] with t ht
  rw [ht]

theorem shortSlopeOperator_integrand_ae (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    ∀ᵐ z ∂planeMeasure, Integrable (fun t => K t*shortSample u f t z) := by
  let H := fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖shortSample u f p.1 p.2‖^2
  have hsm := shortSample_measurable u hu.continuous.measurable f hfm
  have hm : Measurable H := (hKm.comp measurable_fst).norm.mul (hsm.norm.pow_const 2)
  have hzero (p) : 0≤H p := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((shortSample_energy u hu f hfm hf t).1.integrable_norm_pow (by decide : 2≠0)).const_mul ‖K t‖
    · apply (hK.norm.mul_const (4*∫ z, ‖f z‖^2 ∂planeMeasure)).mono'
        hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      simp only [Real.norm_of_nonneg (hzero _)]
      rw [Real.norm_of_nonneg (integral_nonneg fun z => hzero (t,z))]
      change (∫ z, ‖K t‖*‖shortSample u f t z‖^2 ∂planeMeasure)≤_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (shortSample_energy u hu f hfm hf t).2 (norm_nonneg _)
  filter_upwards [hi.prod_left_ae] with z hz
  have hs : Measurable (fun t => shortSample u f t z) := by
    exact hsm.comp (measurable_id.prodMk measurable_const)
  have hc := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖shortSample u f t z‖) hKm.norm hs.norm (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hK.norm hz).1
  exact hc.mono' ((hKm.mul hs).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => le_of_eq (norm_mul _ _))

theorem shortSlopeOperator_sub_ae (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    shortSlopeOperator K u (f-g)=ᵐ[planeMeasure] shortSlopeOperator K u f-shortSlopeOperator K u g := by
  filter_upwards [shortSlopeOperator_integrand_ae K hKm hK u hu f hfm hf,
    shortSlopeOperator_integrand_ae K hKm hK u hu g hgm hg] with z hfz hgz
  have hrep (h : (ℝ×ℝ) → ℂ) : shortSlopeOperator K u h z=∫ t, K t*shortSample u h t z := by
    unfold shortSlopeOperator shortSample
    congr 1
    funext t
    split_ifs <;> simp
  simp only [Pi.sub_apply,hrep]
  rw [←integral_sub hfz hgz]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold shortSample
  split_ifs <;> simp [mul_sub]

end LipschitzHilbert.PacketRepresentation

end

end OAI
