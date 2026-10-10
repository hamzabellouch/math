import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.LocalFieldBootstrapBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

 def thinFieldBase (a b D B : ℝ) : ℝ := localFieldScale a D B+
    localizationIMSConstant*Real.sqrt B/(b^2*a)
 def thinOutMajorant (a b D B : ℝ) : ℝ :=
    1024*localFieldUniversalConstant*thinFieldBase a b D B+
      (512*localFieldUniversalConstant)^2*B/a^2
 def thinFieldMajorant (a b D B : ℝ) : ℝ := localFieldUniversalConstant*
    (thinFieldBase a b D B+(thinOutMajorant a b D B+B/a^2)/2)

namespace CoreObservationEnsemble

lemma thin_observe_field (E : CoreObservationEnsemble) (y z : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hz : z ∈ closedBall y (8*a))
    (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z ≤
      localFieldUniversalConstant*(thinFieldBase a b (max (E.excess Z lam) 0) (E.countMoment y (16*a))+
        Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a) := by
  let E' := E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)
  let B := E.countMoment y (16*a)
  have hzn : ‖z-y‖ ≤ 8*a := mem_closedBall_iff_norm.mp hz
  have hzy : ‖y‖ ≤ ‖z‖+‖z-y‖ := by
    calc ‖y‖ = ‖z-(z-y)‖ := by congr 1; abel
         _ ≤ _ := norm_sub_le _ _
  have hs : 12*a ≤ ‖z‖ := by linarith
  have hf := ensemble_local_field_scale E' z ha hs (by simpa [E',hm] using E.observe_mass (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)) hZ hlam
  have hcount : E'.countMoment z (8*a) ≤ B :=
    (E.observe_countMoment _ _ z (8*a)).trans (E.countMoment_le_of_radius z y (by linarith))
  have he := E.observe_excess_budget y hr hb (by linarith) (R := 16*a) (by linarith) hZ hlam.le
  rw [hm,Real.sqrt_one,mul_one] at he
  have hK : (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2 = localizationIMSConstant/b^2 := by
    unfold localizationIMSConstant
    ring
  rw [hK] at he
  have he' : max (E'.excess Z lam) 0 ≤ max (E.excess Z lam) 0+
      localizationIMSConstant/b^2*Real.sqrt B+
      Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt B := by
    apply max_le
    · exact he.trans (add_le_add (add_le_add (le_max_left _ _) le_rfl) le_rfl)
    · have := localizationIMSConstant_nonneg
      positivity
  have ht := (localFieldScale_mono ha he' hcount)
  have hh := hf.trans (mul_le_mul_of_nonneg_left ht localFieldUniversalConstant_pos.le)
  apply hh.trans_eq
  unfold thinFieldBase localFieldScale
  ring

lemma thin_out_feedback (E : CoreObservationEnsemble) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E.outMoment y hr hb Z lam ≤
      512*localFieldUniversalConstant*(thinFieldBase a b (max (E.excess Z lam) 0) (E.countMoment y (16*a))+
        Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a) := by
  let E' := E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)
  let Q := localFieldUniversalConstant*(thinFieldBase a b (max (E.excess Z lam) 0) (E.countMoment y (16*a))+
        Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a)
  have hh := E.outMoment_spatial y hr hb ha (by linarith : r+b+2*a ≤ ‖y‖)
    (by linarith) hZ hlam.le (ballAverageKernel_measurable a) (ballAverageKernel_nonneg ha)
    (ballAverageKernel_support a) (ballAverageKernel_bound ha)
    (ballAverageKernel_radial a) (ballAverageKernel_mass ha)
  have hi8 := E'.fieldMoment_ball_integrable y ha (by linarith : 8*a+a ≤ ‖y‖) hZ hlam.le
  have hsub : closedBall y (r+b+a) ⊆ closedBall y (8*a) := closedBall_subset_closedBall (by linarith)
  have hinc := setIntegral_mono_set hi8 (ae_of_all _ (fun z => E'.fieldMoment_nonneg Z lam z))
    (ae_of_all _ hsub)
  have hc : IntegrableOn (fun _ : Space => Q) (closedBall y (8*a)) :=
    integrableOn_const (isCompact_closedBall y (8*a)).measure_lt_top.ne
  have hmQ := setIntegral_mono_on hi8 hc isClosed_closedBall.measurableSet
    (fun z hz => E.thin_observe_field y z ha hr hra hb hba hsep hz hm hZ hlam)
  have hp : 0 ≤ 1/(a^3*(Real.pi*4/3)) := by positivity
  have hout := hh.trans (mul_le_mul_of_nonneg_left (hinc.trans hmQ) hp)
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,
    ←Measure.real,space_closedBall_real y (by positivity)] at hout
  have he : 1/(a^3*(Real.pi*4/3))*((8*a)^3*(Real.pi*4/3)*Q) = 512*Q := by
    field_simp [ha.ne',Real.pi_ne_zero]
    ring
  rw [he] at hout
  simpa only [Q,mul_assoc] using hout

theorem thin_out_bound (E : CoreObservationEnsemble) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E.outMoment y hr hb Z lam ≤
      thinOutMajorant a b (max (E.excess Z lam) 0) (E.countMoment y (16*a)) := by
  let X := Real.sqrt (E.outMoment y hr hb Z lam)
  let B := E.countMoment y (16*a)
  let D := 512*localFieldUniversalConstant*Real.sqrt B/a
  let A := 512*localFieldUniversalConstant*thinFieldBase a b (max (E.excess Z lam) 0) B
  have hX : X^2 = E.outMoment y hr hb Z lam := Real.sq_sqrt (E.outMoment_nonneg _ _ _ _ _)
  have hD : D^2 = (512*localFieldUniversalConstant)^2*B/a^2 := by
    dsimp [D]; rw [div_pow,mul_pow,Real.sq_sqrt (E.countMoment_nonneg _ _)]
  have hh := E.thin_out_feedback y ha hr hra hb hba hsep hm hZ hlam
  have hquad : X^2 ≤ A+D*X := by
    rw [hX]
    convert hh using 1; dsimp [A,D,X]; ring
  have hbnd : X^2 ≤ 2*A+D^2 := by nlinarith [sq_nonneg (X-D)]
  rw [hX,hD] at hbnd
  convert hbnd using 1
  unfold thinOutMajorant A B
  ring

theorem thin_field_bound (E : CoreObservationEnsemble) (y z : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hz : z ∈ closedBall y (8*a))
    (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z ≤
      thinFieldMajorant a b (max (E.excess Z lam) 0) (E.countMoment y (16*a)) := by
  have hh := E.thin_observe_field y z ha hr hra hb hba hsep hz hm hZ hlam
  have hbnd := E.thin_out_bound y ha hr hra hb hba hsep hm hZ hlam
  have hX := Real.sq_sqrt (E.outMoment_nonneg y hr hb Z lam)
  have hB := Real.sq_sqrt (E.countMoment_nonneg y (16*a))
  have hs : (Real.sqrt (E.countMoment y (16*a))/a)^2 = E.countMoment y (16*a)/a^2 := by rw [div_pow,hB]
  have hyoung : Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a ≤
      (thinOutMajorant a b (max (E.excess Z lam) 0) (E.countMoment y (16*a))+E.countMoment y (16*a)/a^2)/2 := by
    have h := sq_nonneg (Real.sqrt (E.outMoment y hr hb Z lam)-Real.sqrt (E.countMoment y (16*a))/a)
    have he : Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a =
       Real.sqrt (E.outMoment y hr hb Z lam)*(Real.sqrt (E.countMoment y (16*a))/a) := by ring
    rw [he]
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hyoung) localFieldUniversalConstant_pos.le)

end CoreObservationEnsemble

open MeasureTheory Set Metric

lemma core_field_sq_le_ball_average {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y x : Space) {a R Z lam : ℝ}
    (hR : 0 < R) (hsep : a+2*R ≤ ‖y‖) (hx : ‖x-y‖ ≤ a)
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (max (normalizedCoreField Z lam ψ x) 0)^2 ≤
      (1/(R^3*(Real.pi*4/3)))*∫ z in closedBall y (a+R), (max (normalizedCoreField Z lam ψ z) 0)^2 := by
  let η := ballAverageKernel R
  let B := 1/(R^3*(Real.pi*4/3))
  let F : Space → ℝ := fun z => (max (normalizedCoreField Z lam ψ z) 0)^2
  have hm : Measurable η := ballAverageKernel_measurable R
  have hn := ballAverageKernel_nonneg hR
  have hs := ballAverageKernel_support R
  have hb := ballAverageKernel_bound hR
  have hnuc : 2*R ≤ ‖x‖ := by
    have htri := norm_le_norm_sub_add y x
    rw [norm_sub_rev y x] at htri
    linarith
  have hi := normalizedCoreField_radial_submean_sq hψ hm hR hn hs hb
    (ballAverageKernel_radial R) (ballAverageKernel_mass hR) x hnuc hZ hlam
  apply hi.trans
  let k := translatedDensity η x
  have hkm : Measurable k := translatedDensity_measurable hm _
  have hkn (z : Space) : 0 ≤ k z := hn (z-x)
  have hki : Integrable k := bounded_compact_integrable hkm (isCompact_closedBall _ _)
    (translatedDensity_support hs _) (fun z => hb (z-x))
  have hks : ∀ z, k z ≠ 0 → R ≤ ‖z‖ := by
    intro z hz
    have htri := norm_le_norm_sub_add x z
    rw [norm_sub_rev x z] at htri
    linarith [hs (z-x) hz]
  have hleft := positive_core_pair_integrable hψ hki hkm hkn hZ hlam hR hks 2
  have hFi : IntegrableOn F (closedBall y (a+R)) :=
    core_field_square_ball_integrable hψ y hR (by linarith) hZ hlam
  rw [←integral_const_mul,←integral_indicator isClosed_closedBall.measurableSet]
  apply integral_mono hleft ((integrable_indicator_iff isClosed_closedBall.measurableSet).2 (hFi.const_mul B))
  intro z
  by_cases hz : z ∈ closedBall y (a+R)
  · rw [indicator_of_mem hz]
    simpa only [k,translatedDensity,F,mul_comm] using
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb (z-x)))
        (sq_nonneg (max (normalizedCoreField Z lam ψ z) 0))
  · rw [indicator_of_notMem hz]
    have hk0 : η (z-x) = 0 := by
      by_contra hk
      have hnz := norm_sub_le_norm_sub_add_norm_sub z x y
      have hh := hs (z-x) hk
      exact hz (by rw [mem_closedBall,dist_eq_norm]; linarith)
    simp only [k,translatedDensity,hk0,mul_zero,le_refl]

end CoulombAtom

end

end OAI
