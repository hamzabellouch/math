import Mathlib
import OAI.Analysis.CoulombRadii.Localization.TruncatedCoulomb

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb
noncomputable def meridianMap (p : ℝ × ℝ) : ℝ × ℝ := (Real.sqrt (p.1^2-p.2^2), p.2)
def meridianDomain : Set (ℝ × ℝ) := {p | |p.2| < p.1}
lemma meridianDomain_measurable : MeasurableSet meridianDomain :=
  measurableSet_lt (measurable_snd.abs) measurable_fst
lemma meridian_radicand_pos {p : ℝ × ℝ} (hp : p ∈ meridianDomain) : 0 < p.1^2-p.2^2 := by
  change |p.2| < p.1 at hp
  have h0 := abs_nonneg p.2
  nlinarith [sq_abs p.2]
noncomputable def meridianDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![p.1 / Real.sqrt (p.1^2-p.2^2), -p.2 / Real.sqrt (p.1^2-p.2^2); 0, 1]).toContinuousLinearMap
lemma meridian_hasFDeriv {p : ℝ × ℝ} (hp : p ∈ meridianDomain) :
    HasFDerivAt meridianMap (meridianDeriv p) p := by
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hg : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hh := (Real.hasDerivAt_sqrt (meridian_radicand_pos hp).ne').comp_hasFDerivAt p
    ((hf.pow 2).sub (hg.pow 2))
  have h := hh.prodMk (hasFDerivAt_snd (𝕜:=ℝ) (E:=ℝ) (F:=ℝ))
  unfold meridianDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  apply h.congr_fderiv
  ext <;> simp [div_eq_mul_inv] <;> ring
lemma meridian_det (p : ℝ × ℝ) : (meridianDeriv p).det = p.1 / Real.sqrt (p.1^2-p.2^2) := by
  simp [meridianDeriv, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
lemma meridianMap_injOn : InjOn meridianMap meridianDomain := by
  intro p hp q hq he
  have h1 : Real.sqrt (p.1^2-p.2^2) = Real.sqrt (q.1^2-q.2^2) := congrArg Prod.fst he
  have h2 : p.2 = q.2 := by simpa [meridianMap] using congrArg Prod.snd he
  have hp0 := meridian_radicand_pos hp
  have hq0 := meridian_radicand_pos hq
  rw [Real.sqrt_inj hp0.le hq0.le] at h1
  have hpp : 0 < p.1 := (abs_nonneg p.2).trans_lt hp
  have hqq : 0 < q.1 := (abs_nonneg q.2).trans_lt hq
  apply Prod.ext _ h2
  rw [h2] at h1
  nlinarith
lemma meridian_image : meridianMap '' meridianDomain = Ioi (0:ℝ) ×ˢ (univ : Set ℝ) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Real.sqrt_pos.mpr (meridian_radicand_pos hp), mem_univ _⟩
  · rintro ⟨hq, _⟩
    change 0 < q.1 at hq
    refine ⟨(Real.sqrt (q.1^2+q.2^2), q.2), ?_, ?_⟩
    · change |q.2| < Real.sqrt (q.1^2+q.2^2)
      rw [Real.lt_sqrt (abs_nonneg _)]
      nlinarith [sq_abs q.2, sq_pos_of_pos hq]
    · apply Prod.ext
      · dsimp [meridianMap]
        rw [Real.sq_sqrt (by positivity), add_sub_cancel_right, Real.sqrt_sq hq.le]
      · rfl

lemma meridian_lintegral (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ q in Ioi (0:ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal q.1 * f q) =
      ∫⁻ p in meridianDomain, ENNReal.ofReal p.1 * f (meridianMap p) := by
  rw [← meridian_image, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    meridianDomain_measurable (fun p hp => (meridian_hasFDeriv hp).hasFDerivWithinAt) meridianMap_injOn]
  apply setLIntegral_congr_fun meridianDomain_measurable
  intro p hp
  have hr := meridian_radicand_pos hp
  have hs := Real.sqrt_pos.mpr hr
  have hp0 : 0 < p.1 := (abs_nonneg p.2).trans_lt hp
  dsimp only
  rw [meridian_det, abs_of_pos (div_pos hp0 hs)]
  change ENNReal.ofReal (p.1 / Real.sqrt (p.1^2-p.2^2)) *
    (ENNReal.ofReal (Real.sqrt (p.1^2-p.2^2)) * f _) = _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_pos hp0 hs).le, div_mul_cancel₀ _ hs.ne']

lemma plane_radial_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q : ℝ × ℝ, F (Real.sqrt (q.1^2+q.2^2))) =
      ENNReal.ofReal (2*Real.pi) * ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r * F r := by
  rw [← lintegral_comp_polarCoord_symm]
  have hpoint (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      Real.sqrt ((polarCoord.symm p).1^2+(polarCoord.symm p).2^2) = p.1 := by
    have hr : 0 < p.1 := hp.1
    dsimp [polarCoord]
    rw [show (p.1 * Real.cos p.2)^2 + (p.1 * Real.sin p.2)^2 = p.1^2 from by
      nlinarith [Real.sin_sq_add_cos_sq p.2]]
    exact Real.sqrt_sq hr.le
  calc
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * F p.1 := by
      apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      simp only [smul_eq_mul, hpoint p hp]
    _ = _ := by
      change (∫⁻ p : ℝ × ℝ in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * F p.1) = _
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
      · simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_neg_eq_add]
        rw [show Real.pi + Real.pi = 2*Real.pi by ring, lintegral_mul_const]
        · exact mul_comm _ _
        · exact measurable_id.ennreal_ofReal.mul hF
      · exact ((measurable_fst.ennreal_ofReal).mul (hF.comp measurable_fst)).aemeasurable

lemma axisymmetric_lintegral (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : ℝ, ∫⁻ q : ℝ × ℝ, F (Real.sqrt (z^2+q.1^2+q.2^2), z)) =
      ENNReal.ofReal (2*Real.pi) *
        ∫⁻ p in meridianDomain, ENNReal.ofReal p.1 * F p := by
  have hp (z : ℝ) := plane_radial_lintegral
    (fun r => F (Real.sqrt (z^2+r^2), z))
    (hF.comp (((measurable_const.add (measurable_id.pow_const 2)).sqrt).prodMk measurable_const))
  have he (z : ℝ) : (∫⁻ q : ℝ × ℝ, F (Real.sqrt (z^2+q.1^2+q.2^2), z)) =
      ENNReal.ofReal (2*Real.pi) *
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r * F (Real.sqrt (r^2+z^2), z) := by
    convert hp z using 1
    · apply lintegral_congr
      intro q
      rw [Real.sq_sqrt (by positivity)]
      congr 3
      ring
    · congr 1
      apply lintegral_congr
      intro r
      rw [add_comm (z^2) (r^2)]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (Real.sqrt (p.1^2+p.2^2), p.2)) := by
    exact measurable_fst.ennreal_ofReal.mul
      (hF.comp (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).sqrt.prodMk measurable_snd))
  rw [← lintegral_lintegral_swap hm.aemeasurable]
  rw [← lintegral_prod _ hm.aemeasurable]
  rw [show (volume.restrict (Ioi (0:ℝ))).prod volume =
    (volume : Measure (ℝ × ℝ)).restrict (Ioi (0:ℝ) ×ˢ univ) from by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]]
  rw [meridian_lintegral]
  apply setLIntegral_congr_fun meridianDomain_measurable
  intro p hp
  dsimp [meridianMap]
  rw [Real.sq_sqrt (meridian_radicand_pos hp).le, sub_add_cancel,
    Real.sqrt_sq ((abs_nonneg p.2).trans_lt hp).le]

lemma meridian_lintegral_iterated (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in meridianDomain, ENNReal.ofReal p.1 * F p) =
      ∫⁻ s in Ioi (0:ℝ), ∫⁻ z in Ioo (-s) s, ENNReal.ofReal s * F (s,z) := by
  have hm : Measurable (meridianDomain.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F p)) :=
    (measurable_fst.ennreal_ofReal.mul hF).indicator meridianDomain_measurable
  rw [← lintegral_indicator meridianDomain_measurable, Measure.volume_eq_prod,
    lintegral_prod _ hm.aemeasurable, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s
  · rw [Set.indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs), ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro z
    have he : (s,z) ∈ meridianDomain ↔ z ∈ Ioo (-s) s := by
      change |z| < s ↔ -s < z ∧ z < s
      exact abs_lt
    by_cases hz : z ∈ Ioo (-s) s <;> simp [Set.indicator, he, hz]
  · rw [Set.indicator_of_notMem (show s ∉ Ioi (0:ℝ) from hs)]
    simp [Set.indicator, ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hs)]

noncomputable def tripleSpaceEquiv : (ℝ × (ℝ × ℝ)) ≃ᵐ Space :=
  ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ => ℝ)).symm).trans
    (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm).trans
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))
lemma tripleSpaceEquiv_apply (p : ℝ × (ℝ × ℝ)) :
    tripleSpaceEquiv p = WithLp.toLp 2 ![p.1,p.2.1,p.2.2] := by
  ext i
  fin_cases i <;> rfl
lemma tripleSpaceEquiv_preserving : MeasurePreserving tripleSpaceEquiv volume volume := by
  have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    ((volume_preserving_piFinTwo (fun _ => ℝ)).symm _)
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm _
  have h3 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm _
  exact h3.comp (h2.comp h1)
lemma norm_tripleSpaceEquiv (p : ℝ × (ℝ × ℝ)) :
    ‖tripleSpaceEquiv p‖ = Real.sqrt (p.1^2 + p.2.1^2+p.2.2^2) := by
  rw [tripleSpaceEquiv_apply, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc]
lemma axisymmetric_space_lintegral (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : Space, F (‖x‖, x 0)) = ENNReal.ofReal (2*Real.pi) *
      ∫⁻ p in meridianDomain, ENNReal.ofReal p.1 * F p := by
  rw [← tripleSpaceEquiv_preserving.lintegral_comp_emb tripleSpaceEquiv.measurableEmbedding,
    Measure.volume_eq_prod, lintegral_prod]
  · simp only [norm_tripleSpaceEquiv]
    have he (p : ℝ × (ℝ × ℝ)) : tripleSpaceEquiv p 0 = p.1 := by
      rw [tripleSpaceEquiv_apply]; rfl
    simp_rw [he]
    exact axisymmetric_lintegral F hF
  · have hm : Measurable (fun x : Space => F (‖x‖, x 0)) :=
      hF.comp (measurable_norm.prodMk (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable)
    exact (hm.comp tripleSpaceEquiv.measurable).aemeasurable

lemma angular_coulomb_integral {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (1/2:ℝ) * (∫ u in (-1:ℝ)..1, (r^2+s^2-2*r*s*u)^(-(1/2):ℝ)) = (max r s)⁻¹ := by
  have H := intervalIntegral.mul_integral_comp_sub_mul (f := fun x : ℝ => x^(-(1/2):ℝ))
    (a := -1) (b := 1) (2*r*s) (r^2+s^2)
  have h1 : r^2+s^2-(2*r*s)*1 = (r-s)^2 := by ring
  have h2 : r^2+s^2-(2*r*s)*(-1) = (r+s)^2 := by ring
  rw [h1, h2, integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))] at H
  norm_num only [show (-(1/2):ℝ)+1 = 1/2 by norm_num] at H
  simp_rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs] at H
  rw [abs_of_pos (add_pos hr hs)] at H
  rcases le_total r s with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)] at *
    field_simp
    nlinarith
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)] at *
    field_simp
    nlinarith

lemma affine_halfpower_intervalIntegrable (d c a b : ℝ) (hc : c ≠ 0) :
    IntervalIntegrable (fun z => (d-c*z)^(-(1/2):ℝ)) volume a b := by
  have H := ((intervalIntegral.intervalIntegrable_rpow'
    (a:=d-c*a) (b:=d-c*b) (by norm_num : (-1:ℝ) < -(1/2))).comp_sub_left d).comp_mul_left (c:=c)
  convert H using 1 <;> field_simp <;> ring

lemma meridian_coulomb_integral {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ z in (-s)..s, (r^2+s^2-2*r*z)^(-(1/2):ℝ)) = 2*s*(max r s)⁻¹ := by
  have H := intervalIntegral.integral_comp_mul_left (a:=(-1:ℝ)) (b:=1)
    (c:=s) (fun z => (r^2+s^2-2*r*z)^(-(1/2):ℝ)) hs.ne'
  have he (u : ℝ) : r^2+s^2-2*r*(s*u) = r^2+s^2-2*r*s*u := by ring
  simp_rw [he] at H
  simp only [mul_neg_one, mul_one, smul_eq_mul] at H
  have A := angular_coulomb_integral hr hs
  rw [H] at A
  have hsi : s*s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  calc
    _ = s * (s⁻¹ * ∫ z in (-s)..s, (r^2+s^2-2*r*z)^(-(1/2):ℝ)) := by rw [← mul_assoc, hsi, one_mul]
    _ = _ := by nlinarith

lemma meridian_coulomb_lintegral {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫⁻ z in Ioo (-s) s, ENNReal.ofReal ((r^2+s^2-2*r*z)^(-(1/2):ℝ))) =
      ENNReal.ofReal (2*s*(max r s)⁻¹) := by
  have hab : -s ≤ s := by linarith
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
    (affine_halfpower_intervalIntegrable (r^2+s^2) (2*r) (-s) s (by positivity))
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hab,
      meridian_coulomb_integral hr hs]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact Real.rpow_nonneg (by nlinarith [sq_nonneg (r-s), hz.2]) _

lemma norm_axis_sub_rpow (r : ℝ) (x : Space) :
    ‖EuclideanSpace.single 0 r - x‖⁻¹ =
      (r^2+‖x‖^2-2*r*x 0)^(-(1/2):ℝ) := by
  have he : ‖EuclideanSpace.single 0 r - x‖^2 = r^2+‖x‖^2-2*r*x 0 := by
    rw [norm_sub_sq_real]
    simp [EuclideanSpace.inner_single_left, Real.norm_eq_abs, sq_abs]
    ring
  rw [← he, Real.rpow_neg (sq_nonneg _) (1/2:ℝ), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _)]

lemma radial_axis_coulomb_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : Space, ENNReal.ofReal ‖EuclideanSpace.single 0 r-x‖⁻¹ * F ‖x‖) =
      ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2*(max r s)⁻¹) * F s := by
  simp_rw [norm_axis_sub_rpow]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((r^2+p.1^2-2*r*p.2)^(-(1/2):ℝ)) * F p.1) := by fun_prop
  rw [axisymmetric_space_lintegral _ hm, meridian_lintegral_iterated _ hm]
  have he (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) :
      (∫⁻ z in Ioo (-s) s, ENNReal.ofReal s *
        (ENNReal.ofReal ((r^2+s^2-2*r*z)^(-(1/2):ℝ)) * F s)) =
      ENNReal.ofReal 2 * (ENNReal.ofReal (s^2*(max r s)⁻¹) * F s) := by
    change 0 < s at hs
    rw [lintegral_const_mul _ (by fun_prop), lintegral_mul_const _ (by fun_prop),
      meridian_coulomb_lintegral hr hs]
    calc
      _ = ENNReal.ofReal (s*(2*s*(max r s)⁻¹))*F s := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hs.le]
      _ = ENNReal.ofReal (2*(s^2*(max r s)⁻¹))*F s := by congr 2; ring
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Ioi he, lintegral_const_mul _ (by fun_prop),
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

lemma radial_space_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : Space, F ‖x‖) = ENNReal.ofReal (4*Real.pi) *
      ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2) * F s := by
  have hm : Measurable (fun p : ℝ × ℝ => F p.1) := hF.comp measurable_fst
  rw [axisymmetric_space_lintegral _ hm, meridian_lintegral_iterated _ hm]
  have he (s : ℝ) (hs : s ∈ Ioi (0:ℝ)) :
      (∫⁻ z in Ioo (-s) s, ENNReal.ofReal s * F s) =
      ENNReal.ofReal 2 * (ENNReal.ofReal (s^2) * F s) := by
    change 0 < s at hs
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    rw [show s- -s = 2*s by ring, mul_comm (ENNReal.ofReal s * F s),
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 2
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi he, lintegral_const_mul _ (by fun_prop),
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

lemma radial_coulomb_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {x : Space} (hx : x ≠ 0) :
    (∫⁻ y : Space, ENNReal.ofReal ‖x-y‖⁻¹ * F ‖y‖) =
      ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2*(max ‖x‖ s)⁻¹) * F s := by
  let v : Space := EuclideanSpace.single 0 ‖x‖
  let E := (ℝ ∙ (v-x))ᗮ.reflection
  have hv : ‖v‖ = ‖x‖ := by simp [v]
  have hE : E v = x := Submodule.reflection_sub hv
  calc
    _ = ∫⁻ y : Space, ENNReal.ofReal ‖x-E y‖⁻¹ * F ‖E y‖ :=
      (E.measurePreserving.lintegral_comp_emb E.toHomeomorph.measurableEmbedding _).symm
    _ = ∫⁻ y : Space, ENNReal.ofReal ‖v-y‖⁻¹ * F ‖y‖ := by
      apply lintegral_congr
      intro y
      rw [← hE, ← E.map_sub, E.norm_map, E.norm_map]
    _ = _ := radial_axis_coulomb_lintegral F hF (norm_pos_iff.mpr hx)

lemma radial_coulomb_lintegral_le (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {x : Space} (hx : x ≠ 0) :
    (∫⁻ y : Space, ENNReal.ofReal ‖x-y‖⁻¹ * F ‖y‖) ≤
      ENNReal.ofReal ‖x‖⁻¹ * ∫⁻ y : Space, F ‖y‖ := by
  calc
    _ = ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2*(max ‖x‖ s)⁻¹) * F s :=
      radial_coulomb_lintegral F hF hx
    _ ≤ ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (‖x‖⁻¹*s^2) * F s := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Ioi
      intro s _
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left
        (inv_anti₀ (norm_pos_iff.mpr hx) (le_max_left ‖x‖ s)) (sq_nonneg s)]
    _ = _ := by
      rw [radial_space_lintegral F hF]
      simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg x)), mul_assoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      ac_rfl

lemma radial_coulomb_lintegral_eq (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {R : ℝ} (hFR : ∀ s, R < s → F s = 0)
    {x : Space} (hx : x ≠ 0) (hRx : R ≤ ‖x‖) :
    (∫⁻ y : Space, ENNReal.ofReal ‖x-y‖⁻¹ * F ‖y‖) =
      ENNReal.ofReal ‖x‖⁻¹ * ∫⁻ y : Space, F ‖y‖ := by
  calc
    _ = ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2*(max ‖x‖ s)⁻¹) * F s :=
      radial_coulomb_lintegral F hF hx
    _ = ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (‖x‖⁻¹*s^2) * F s := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s _
      dsimp only
      by_cases hs : R < s
      · simp [hFR s hs]
      · rw [max_eq_left ((le_of_not_gt hs).trans hRx), mul_comm (s^2)]
    _ = _ := by
      rw [radial_space_lintegral F hF]
      simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg x)), mul_assoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      ac_rfl

lemma space_axis_continuous : Continuous (fun s : ℝ => (EuclideanSpace.single (0 : Fin 3) s : Space)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  simp only [Pi.single_apply]
  split <;> fun_prop

lemma radial_coulomb_integral_le {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ} (hfM : ∀ y, f y ≤ M)
    (hrad : ∀ y, f y = f (EuclideanSpace.single 0 ‖y‖))
    {x : Space} (hx : x ≠ 0) :
    (∫ y, coulombKernel (x-y) * f y) ≤ coulombKernel x * ∫ y, f y := by
  let F : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (f (EuclideanSpace.single 0 s))
  have hmF : Measurable F := (hm.comp space_axis_continuous.measurable).ennreal_ofReal
  have he (y : Space) : F ‖y‖ = ENNReal.ofReal (f y) := congrArg ENNReal.ofReal (hrad y).symm
  have H := radial_coulomb_lintegral_le F hmF hx
  simp_rw [he] at H
  have hi := coulomb_convolution_integrable hf hm hf0 hfM (by norm_num : (0:ℝ) < 1) x
  have hp (y : Space) : 0 ≤ coulombKernel (x-y)*f y := mul_nonneg (coulombKernel_nonneg _) (hf0 _)
  have hI := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp)
  have hmass := ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0)
  simp_rw [ENNReal.ofReal_mul (coulombKernel_nonneg _)] at hI
  change ENNReal.ofReal (∫ y, coulombKernel (x-y)*f y) =
    ∫⁻ y, ENNReal.ofReal ‖x-y‖⁻¹*ENNReal.ofReal (f y) at hI
  rw [← hI, ← hmass, ← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))] at H
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (coulombKernel_nonneg x) (integral_nonneg hf0))).mp H

lemma radial_coulomb_integral_eq {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ} (hfM : ∀ y, f y ≤ M)
    (hrad : ∀ y, f y = f (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 ≤ R) (hfs : ∀ y, R < ‖y‖ → f y = 0)
    {x : Space} (hx : x ≠ 0) (hRx : R ≤ ‖x‖) :
    (∫ y, coulombKernel (x-y) * f y) = coulombKernel x * ∫ y, f y := by
  let F : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (f (EuclideanSpace.single 0 s))
  have hmF : Measurable F := (hm.comp space_axis_continuous.measurable).ennreal_ofReal
  have he (y : Space) : F ‖y‖ = ENNReal.ofReal (f y) := congrArg ENNReal.ofReal (hrad y).symm
  have hs : ∀ s, R < s → F s = 0 := by
    intro s hs
    have hsp : 0 < s := hR.trans_lt hs
    have h := hfs (EuclideanSpace.single 0 s) (by simpa [Real.norm_eq_abs, abs_of_pos hsp] using hs)
    simp only [F, h, ENNReal.ofReal_zero]
  have H := radial_coulomb_lintegral_eq F hmF hs hx hRx
  simp_rw [he] at H
  have hi := coulomb_convolution_integrable hf hm hf0 hfM (by norm_num : (0:ℝ) < 1) x
  have hp (y : Space) : 0 ≤ coulombKernel (x-y)*f y := mul_nonneg (coulombKernel_nonneg _) (hf0 _)
  have hI := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp)
  have hmass := ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0)
  simp_rw [ENNReal.ofReal_mul (coulombKernel_nonneg _)] at hI
  change ENNReal.ofReal (∫ y, coulombKernel (x-y)*f y) =
    ∫⁻ y, ENNReal.ofReal ‖x-y‖⁻¹*ENNReal.ofReal (f y) at hI
  rw [← hI, ← hmass, ← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))] at H
  change ENNReal.ofReal (∫ y, coulombKernel (x-y)*f y) =
    ENNReal.ofReal (coulombKernel x * ∫ y, f y) at H
  have H' := congrArg ENNReal.toReal H
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hp),
    ENNReal.toReal_ofReal (mul_nonneg (coulombKernel_nonneg x) (integral_nonneg hf0))] using H'

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
