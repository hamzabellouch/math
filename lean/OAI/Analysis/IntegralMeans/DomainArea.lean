import OAI.Analysis.IntegralMeans.PositiveArea

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma schlicht_area {f : ℂ → ℂ} (hf : Schlicht f) {t : ℝ}
    (ht : -2 < t) (ht2 : t < 2/3) : IntegrableOn (fun z => ‖deriv f z‖^t) disk := by
  rcases lt_trichotomy t 0 with h | h | h
  · exact schlicht_negative_area hf ht h
  · subst t
    simp only [Real.rpow_zero]
    exact integrableOn_const (by
      apply ne_of_lt
      exact Metric.isBounded_ball.measure_lt_top)
  · exact schlicht_positive_area hf h ht2

def normalizeDisk (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z-f 0)/deriv f 0

lemma normalizeDisk_hasDeriv {f : ℂ → ℂ} (hf : UnivalentOn f disk) {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt (normalizeDisk f) (deriv f z/deriv f 0) z :=
  ((hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const (f 0)).div_const _

lemma normalizeDisk_schlicht {f : ℂ → ℂ} (hf : UnivalentOn f disk) : Schlicht (normalizeDisk f) := by
  have h0 : (0:ℂ) ∈ disk := by simp [disk]
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf h0
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro z hz
    exact (normalizeDisk_hasDeriv hf hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    have hh : f z-f 0 = f w-f 0 := (div_left_inj' hn).mp he
    exact hf.2 hz hw (sub_left_inj.mp hh)
  · simp [normalizeDisk]
  · rw [(normalizeDisk_hasDeriv hf h0).deriv,div_self hn]

lemma univalent_disk_area {f : ℂ → ℂ} (hf : UnivalentOn f disk) {t : ℝ}
    (ht : -2 < t) (ht2 : t < 2/3) : IntegrableOn (fun z => ‖deriv f z‖^t) disk := by
  have h0 : (0:ℂ) ∈ disk := by simp [disk]
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf h0
  have hg := schlicht_area (normalizeDisk_schlicht hf) ht ht2
  apply IntegrableOn.congr_fun (hg.const_mul (‖deriv f 0‖^t)) _ Metric.isOpen_ball.measurableSet
  intro z hz
  have he : deriv f z = deriv f 0 * deriv (normalizeDisk f) z := by
    rw [(normalizeDisk_hasDeriv hf hz).deriv]
    field_simp
  dsimp only
  rw [he,norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma univalent_inverse_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : UnivalentOn φ U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (Function.invFunOn φ U) (deriv φ z)⁻¹ (φ z) := by
  have ha := hφ.1.analyticOnNhd hU z hz
  apply (ha.hasStrictDerivAt.to_local_left_inverse (univalent_deriv_ne_zero hU hφ hz) ?_).hasDerivAt
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hφ.2.leftInvOn_invFunOn hw

lemma bijOn_inverse_univalent {U V : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) (hb : BijOn φ U V) :
    UnivalentOn (Function.invFunOn φ U) V := by
  constructor
  · intro w hw
    obtain ⟨z,hz,rfl⟩ := hb.surjOn hw
    exact (univalent_inverse_hasDerivAt hU ⟨hφ,hb.injOn⟩ hz).differentiableAt.differentiableWithinAt
  · exact (Function.invFunOn_injOn_image φ U).mono hb.surjOn

lemma bijOn_inverse_image {U V : Set ℂ} {φ : ℂ → ℂ} (hb : BijOn φ U V) :
    Function.invFunOn φ U '' V = U := by
  rw [← hb.image_eq]
  exact hb.injOn.invFunOn_image (Subset.refl _)

lemma conformal_lintegral_eq {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ w in F '' s, b w) = ∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b]
  apply setLIntegral_congr_fun hs
  intro z hz
  have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
  have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
  dsimp only
  have hd' : (fderiv ℝ F z).det = ‖deriv F z‖^2 := det_fderiv_complex (hF z hz)
  rw [hf,hd',abs_of_nonneg (sq_nonneg _)]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma conformal_domain_area {W : Set ℂ} (hW : IsOpen W) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ W) (hb : BijOn φ W disk) {s : ℝ}
    (hs : 4/3 < s) (hs4 : s < 4) : IntegrableOn (fun z => ‖deriv φ z‖^s) W := by
  let f := Function.invFunOn φ W
  have hf : UnivalentOn f disk := bijOn_inverse_univalent hW hφ hb
  have himage : f '' disk = W := bijOn_inverse_image hb
  have hfi : IntegrableOn (fun w => ‖deriv f w‖^(2-s)) disk := univalent_disk_area hf (by linarith) (by linarith)
  have hderiv (w : ℂ) (hw : w ∈ disk) : deriv φ (f w) = (deriv f w)⁻¹ := by
    have hz : f w ∈ W := hb.surjOn.mapsTo_invFunOn hw
    have hv : φ (f w) = w := hb.surjOn.rightInvOn_invFunOn hw
    have hd := (univalent_inverse_hasDerivAt hW ⟨hφ,hb.injOn⟩ hz).deriv
    change deriv f (φ (f w)) = (deriv φ (f w))⁻¹ at hd
    rw [hv] at hd
    rw [hd,inv_inv]
  have hc : ContinuousOn (fun z => ‖deriv φ z‖^s) W := by
    apply (hφ.deriv hW).continuousOn.norm.rpow_const
    intro z hz
    exact Or.inl (norm_ne_zero_iff.mpr (univalent_deriv_ne_zero hW ⟨hφ,hb.injOn⟩ hz))
  refine ⟨hc.aestronglyMeasurable hW.measurableSet,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun z : ℂ => Real.rpow_nonneg (norm_nonneg _) s))).mpr
  have he := conformal_lintegral_eq Metric.isOpen_ball.measurableSet
    (fun z hz => hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)) hf.2
    (fun z => ENNReal.ofReal (‖deriv φ z‖^s))
  change (∫⁻ z in f '' disk, ENNReal.ofReal (‖deriv φ z‖^s)) =
    ∫⁻ z in disk, ENNReal.ofReal (‖deriv f z‖^2)*ENNReal.ofReal (‖deriv φ (f z)‖^s) at he
  rw [himage] at he
  rw [he]
  have hp : (∫⁻ w in disk, ENNReal.ofReal (‖deriv f w‖^2)*ENNReal.ofReal (‖deriv φ (f w)‖^s)) =
      ∫⁻ w in disk, ENNReal.ofReal (‖deriv f w‖^(2-s)) := by
    apply setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro w hw
    dsimp only
    rw [hderiv w hw,norm_inv,Real.inv_rpow (norm_nonneg _),← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    have hn : 0 < ‖deriv f w‖ := norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball hf hw)
    rw [← Real.rpow_natCast ‖deriv f w‖ 2,← Real.rpow_neg hn.le,← Real.rpow_add hn]
    rfl
  rw [hp]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun w : ℂ => Real.rpow_nonneg (norm_nonneg (deriv f w)) (2-s)))).mp hfi.hasFiniteIntegral

end Brennan

end

end OAI
