import Mathlib
import OAI.Analysis.Crouzeix.AngularRadius
import OAI.Analysis.Crouzeix.ExteriorContour

namespace OAI

/-! Faber. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma twice_coordinate_mem (t : CircleSpace) : C.radius < ‖2 * circleCoordinate t‖ := by
  rw [norm_mul, norm_circleCoordinate, mul_one, norm_ofNat]
  exact C.radius_lt_one.trans (by norm_num)

def outerMap : C(CircleSpace, ℂ) :=
  ⟨fun t => C.G (2 * circleCoordinate t),
    C.analytic.continuousOn.comp_continuous
      (continuous_const.mul circleCoordinate.continuous) C.twice_coordinate_mem⟩

def outerDomain : Set ℂ := (range C.outerMap)ᶜ

lemma isOpen_outerDomain : IsOpen C.outerDomain :=
  (isCompact_range C.outerMap.continuous).isClosed.isOpen_compl

lemma closure_subset_outerDomain : closure U ⊆ C.outerDomain := by
  rintro z hz ⟨t, rfl⟩
  exact C.outside.mapsTo (by
    change 1 < ‖2 * circleCoordinate t‖
    rw [norm_mul, norm_ofNat, norm_circleCoordinate, mul_one]
    norm_num) hz

lemma outer_difference_ne_zero {z : ℂ} (hz : z ∈ C.outerDomain) (t : CircleSpace) :
    C.G (2 * circleCoordinate t) - z ≠ 0 := by
  intro he
  exact hz ⟨t, sub_eq_zero.mp he⟩

def physicalCoefficient (j : ℤ) (z : ℂ) : ℂ :=
  ∫ t, (2 * circleCoordinate t)^j *
    ((2 * circleCoordinate t * deriv C.G (2 * circleCoordinate t)) /
      (C.G (2 * circleCoordinate t) - z)) ∂circleMeasure

lemma differentiableOn_physicalCoefficient (j : ℤ) :
    DifferentiableOn ℂ (C.physicalCoefficient j) C.outerDomain := by
  have hq : Continuous (fun t : CircleSpace =>
      2 * circleCoordinate t * deriv C.G (2 * circleCoordinate t)) :=
    (continuous_const.mul circleCoordinate.continuous).mul
      (C.analytic.deriv.continuousOn.comp_continuous
        (continuous_const.mul circleCoordinate.continuous) C.twice_coordinate_mem)
  apply differentiableOn_parameter_circleIntegral C.isOpen_outerDomain
  · exact ((continuous_const.mul (circleCoordinate.continuous.comp continuous_snd)).continuousOn.zpow₀ j
        (fun p _ => Or.inl (mul_ne_zero (by norm_num) (circleCoordinate_ne_zero p.2)))).mul
      ((hq.comp continuous_snd).continuousOn.div
        ((C.outerMap.continuous.comp continuous_snd).sub continuous_fst).continuousOn
        (fun p hp => C.outer_difference_ne_zero hp.1 p.2))
  · intro t
    exact (differentiableOn_const _).mul
      ((differentiableOn_const _).div ((differentiableOn_const _).sub differentiableOn_id)
        (fun z hz => C.outer_difference_ne_zero hz t))

lemma physicalCoefficient_inside (hU : IsOpen U) (j : ℤ) {z : ℂ} (hz : z ∈ U) :
    C.physicalCoefficient j z =
      ∫ t, (circleCoordinate t)^j * (C.boundaryNormal t /
        (C.boundaryMap t - z)) ∂circleMeasure := by
  have hsub : closedBall (0 : ℂ) 2 \ ball 0 1 ⊆ {t | C.radius < ‖t‖} := by
    intro t ht
    exact C.radius_lt_one.trans_le (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2))
  have hn : ∀ t ∈ closedBall (0 : ℂ) 2 \ ball 0 1, C.G t - z ≠ 0 := by
    intro t ht
    exact sub_ne_zero.mpr (fun he => C.exterior_value_not_mem hU
      (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2)) (he ▸ hz))
  have hs : ball (0 : ℂ) 2 \ closedBall 0 1 ⊆ closedBall (0 : ℂ) 2 \ ball 0 1 :=
    fun t ht => ⟨ball_subset_closedBall ht.1, fun he => ht.2 (ball_subset_closedBall he)⟩
  have he := integral_laurent_deform (f := fun t => t * deriv C.G t / (C.G t - z))
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)
    ((continuousOn_id.mul (C.analytic.deriv.continuousOn.mono hsub)).div
      ((C.analytic.continuousOn.mono hsub).sub continuousOn_const) hn)
    ((differentiableOn_id.mul (C.analytic.deriv.differentiableOn.mono (hs.trans hsub))).div
      ((C.analytic.differentiableOn.mono (hs.trans hsub)).sub_const z)
      (fun t ht => hn t (hs ht))) j
  simpa only [ofReal_ofNat, ofReal_one, one_mul, smul_eq_mul, physicalCoefficient,
    boundaryNormal, boundaryMap, ContinuousMap.coe_mk] using he

lemma physicalCoefficient_inside_neg (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    {n : ℕ} (hn : n ≠ 0) : C.physicalCoefficient (-(n : ℤ)) z = 0 := by
  rw [C.physicalCoefficient_inside hU _ hz]
  simp_rw [← C.reciprocalCauchy_boundary hU hz, zpow_neg, zpow_natCast, ← inv_pow]
  rw [integral_holomorphic_inverse_circleCoordinate (f := fun u => u^n * C.reciprocalCauchy z u)
    ((differentiableOn_id.pow n).mul (C.differentiableOn_reciprocalCauchy hU hz))]
  simp [zero_pow hn]

lemma physicalCoefficient_inside_zero (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    C.physicalCoefficient 0 z = 1 := by
  rw [C.physicalCoefficient_inside hU _ hz]
  simp_rw [zpow_zero, one_mul, ← C.reciprocalCauchy_boundary hU hz]
  rw [integral_holomorphic_inverse_circleCoordinate (C.differentiableOn_reciprocalCauchy hU hz)]
  simp [reciprocalCauchy, reciprocalDenominator, C.leading_ne_zero]

def correctionMoment (j : ℕ) (v : ℂ) : ℂ :=
  ∫ t, (circleCoordinate t)^j * C.correction (circleCoordinate t)⁻¹ v ∂circleMeasure

lemma continuousOn_correctionMoment_integrand (j : ℕ) :
    ContinuousOn (Function.uncurry (fun v (t : CircleSpace) =>
      (circleCoordinate t)^j * C.correction (circleCoordinate t)⁻¹ v))
      (C.reciprocalDisk ×ˢ univ) := by
  apply ContinuousOn.mul
  · exact ((circleCoordinate.continuous.comp continuous_snd).pow j).continuousOn
  · have hc : Continuous (fun p : ℂ × CircleSpace => ((circleCoordinate p.2)⁻¹,p.1)) :=
      ((circleCoordinate.continuous.comp continuous_snd).inv₀
        (fun p => circleCoordinate_ne_zero p.2)).prodMk continuous_fst
    have hi : MapsTo (fun p : ℂ × CircleSpace => ((circleCoordinate p.2)⁻¹,p.1))
        (C.reciprocalDisk ×ˢ univ) (C.reciprocalDisk ×ˢ C.reciprocalDisk) :=
      fun p hp => ⟨C.circle_inverse_mem p.2, hp.1⟩
    exact C.continuousOn_correction.comp
      (f := fun p : ℂ × CircleSpace => ((circleCoordinate p.2)⁻¹,p.1)) hc.continuousOn hi

lemma differentiableOn_correctionMoment_integrand (j : ℕ) (t : CircleSpace) :
    DifferentiableOn ℂ (fun v =>
      (circleCoordinate t)^j * C.correction (circleCoordinate t)⁻¹ v) C.reciprocalDisk := by
  exact (C.differentiableOn_correction_right (C.circle_inverse_mem t)).const_mul _

lemma differentiableOn_correctionMoment (j : ℕ) :
    DifferentiableOn ℂ (C.correctionMoment j) C.reciprocalDisk := by
  unfold correctionMoment
  apply differentiableOn_parameter_circleIntegral (E := ℂ) isOpen_ball
  · exact C.continuousOn_correctionMoment_integrand j
  · exact C.differentiableOn_correctionMoment_integrand j

@[simp] lemma correctionMoment_zero (j : ℕ) : C.correctionMoment j 0 = 0 := by
  simp [correctionMoment]

lemma correctionMoment_zero_index (v : ℂ) (hv : v ∈ C.reciprocalDisk) :
    C.correctionMoment 0 v = 0 := by
  simp only [correctionMoment, pow_zero, one_mul]
  rw [integral_holomorphic_inverse_circleCoordinate
    ((C.differentiableOn_correction_left hv).mono C.closed_unit_subset_reciprocalDisk)]
  exact C.correction_zero_left v

lemma physicalCoefficient_closed_neg (hU : IsOpen U) {z : ℂ} (hz : z ∈ closure U)
    {n : ℕ} (hn : n ≠ 0) : C.physicalCoefficient (-(n : ℤ)) z = 0 := by
  exact (Set.EqOn.of_subset_closure
    (fun _ hy => C.physicalCoefficient_inside_neg hU hy hn)
    ((C.differentiableOn_physicalCoefficient _).continuousOn.mono C.closure_subset_outerDomain)
    continuousOn_const subset_closure (Subset.refl _)) hz

lemma physicalCoefficient_closed_zero (hU : IsOpen U) {z : ℂ} (hz : z ∈ closure U) :
    C.physicalCoefficient 0 z = 1 := by
  exact (Set.EqOn.of_subset_closure
    (fun _ hy => C.physicalCoefficient_inside_zero hU hy)
    ((C.differentiableOn_physicalCoefficient _).continuousOn.mono C.closure_subset_outerDomain)
    continuousOn_const subset_closure (Subset.refl _)) hz

lemma correctionMoment_outer (j : ℕ) {v : ℂ} (hv : v ∈ C.reciprocalDisk) :
    (∫ t, (2 * circleCoordinate t)^j *
      C.correction (2 * circleCoordinate t)⁻¹ v ∂circleMeasure) = C.correctionMoment j v := by
  have hs : closedBall (0 : ℂ) 2 \ ball 0 1 ⊆ {t | C.radius < ‖t‖} := by
    intro t ht
    exact C.radius_lt_one.trans_le (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2))
  have hn : ∀ t ∈ closedBall (0 : ℂ) 2 \ ball 0 1, t ≠ 0 := fun t ht =>
    norm_pos_iff.mp (C.radius_pos.trans (hs ht))
  have hi : MapsTo (fun t : ℂ => t⁻¹) (closedBall 0 2 \ ball 0 1) C.reciprocalDisk :=
    fun t ht => C.inverse_mem_reciprocalDisk (hs ht)
  have hd : DifferentiableOn ℂ (fun t : ℂ => C.correction t⁻¹ v) (closedBall 0 2 \ ball 0 1) :=
    (C.differentiableOn_correction_left hv).comp (differentiableOn_id.inv hn) hi
  have he := integral_laurent_deform (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 2) hd.continuousOn
    (hd.mono (fun t ht => ⟨ball_subset_closedBall ht.1, fun he => ht.2 (ball_subset_closedBall he)⟩)) (j : ℤ)
  simpa only [smul_eq_mul, ofReal_ofNat, ofReal_one, one_mul, zpow_natCast, correctionMoment] using he

lemma circle_model_moment (j : ℕ) {w : ℂ} (hw : ‖w‖ < 2) :
    (∫ t, (2 * circleCoordinate t)^j *
      (2 * circleCoordinate t / (2 * circleCoordinate t - w)) ∂circleMeasure) = w^j := by
  have hc := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (f := fun z : ℂ => z^j) countable_empty (mem_ball_zero_iff.mpr hw)
    (continuous_id.pow j).continuousOn
    (fun z _ => (differentiableAt_id.pow j))
  have he := integral_scaled_coordinate_cauchy (fun z : ℂ => (z-w)⁻¹ • z^j)
    (by norm_num : (0 : ℝ) < 2)
  rw [hc] at he
  convert he using 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [ofReal_ofNat, smul_eq_mul, div_eq_mul_inv]
  ring

lemma physicalCoefficient_boundary (j : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    C.physicalCoefficient (j : ℤ) (C.G w) = w^j + C.correctionMoment j w⁻¹ := by
  have hwC : C.radius < ‖w‖ := hw.symm ▸ C.radius_lt_one
  have hdiff (t : CircleSpace) : 2 * circleCoordinate t ≠ w := by
    intro he
    have hnorm := congrArg norm he
    rw [norm_mul, norm_ofNat, norm_circleCoordinate, mul_one, hw] at hnorm
    norm_num at hnorm
  have hsplit (t : CircleSpace) :
      (2 * circleCoordinate t)^j *
        ((2 * circleCoordinate t * deriv C.G (2 * circleCoordinate t)) /
          (C.G (2 * circleCoordinate t) - C.G w)) =
      (2 * circleCoordinate t)^j * (2 * circleCoordinate t / (2 * circleCoordinate t - w)) +
      (2 * circleCoordinate t)^j * C.correction (2 * circleCoordinate t)⁻¹ w⁻¹ := by
    rw [C.correction_eq (C.twice_coordinate_mem t) hwC (hdiff t)]
    ring
  have hc1 : Continuous (fun t : CircleSpace =>
      (2 * circleCoordinate t)^j * (2 * circleCoordinate t / (2 * circleCoordinate t - w))) :=
    ((continuous_const.mul circleCoordinate.continuous).pow j).mul
      ((continuous_const.mul circleCoordinate.continuous).div
        ((continuous_const.mul circleCoordinate.continuous).sub continuous_const)
        (fun t => sub_ne_zero.mpr (hdiff t)))
  have hc2 : Continuous (fun t : CircleSpace =>
      (2 * circleCoordinate t)^j * C.correction (2 * circleCoordinate t)⁻¹ w⁻¹) :=
    ((continuous_const.mul circleCoordinate.continuous).pow j).mul
      (C.continuousOn_correction.comp_continuous
        (((continuous_const.mul circleCoordinate.continuous).inv₀
          (fun t => mul_ne_zero (by norm_num) (circleCoordinate_ne_zero t))).prodMk continuous_const)
        (fun t => ⟨C.inverse_mem_reciprocalDisk (C.twice_coordinate_mem t), C.inverse_mem_reciprocalDisk hwC⟩))
  simp only [physicalCoefficient, zpow_natCast, hsplit]
  rw [integral_add (hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    circle_model_moment j (by rw [hw]; norm_num), C.correctionMoment_outer j (C.inverse_mem_reciprocalDisk hwC)]

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
