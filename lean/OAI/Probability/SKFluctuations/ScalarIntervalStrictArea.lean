import Mathlib
import OAI.Probability.SKFluctuations.FinitePrefixRoot

namespace OAI

/-! Scalar Interval Strict Area. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem intervalIntegral_pos_of_interior_interval {f : ℝ → ℝ} {p r u v : ℝ}
    (hpu : p ≤ u) (huv : u < v) (hvr : v ≤ r) (hi : IntervalIntegrable f volume p r)
    (hn : ∀ s ∈ Ioo p r, 0 ≤ f s) (hp : ∀ s ∈ Ioo u v, 0 < f s) :
    0 < ∫ s in p..r, f s := by
  have hpr := hpu.trans_lt (huv.trans_le hvr)
  have h₀ : 0 ≤ᵐ[volume.restrict (uIoc p r)] f := by
    rw [EventuallyLE,uIoc_of_le hpr.le]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs using hn s hs
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' h₀ hi]
  refine ⟨hpr,((Measure.measure_Ioo_pos volume).mpr huv).trans_le (measure_mono ?_)⟩
  intro s hs
  exact ⟨Function.mem_support.mpr (hp s hs).ne',hpu.trans_lt hs.1,hs.2.le.trans hvr⟩

 theorem scalarInterval_down_area_pos (α : boundedMassProfiles) {p r u : ℝ}
    (hpu : p < u) (hur : u < r) (hu : α.val p < α.val u) :
    0 < ∫ s in p..r, α.val s-α.val p := by
  apply intervalIntegral_pos_of_interior_interval hpu.le hur le_rfl
    (α.property.2.intervalIntegrable.sub intervalIntegrable_const)
  · intro s hs
    exact sub_nonneg.mpr (α.property.2 hs.1.le)
  · intro s hs
    exact sub_pos.mpr (hu.trans_le (α.property.2 hs.1.le))

 theorem scalarInterval_up_area_neg (α : boundedMassProfiles) {p r u : ℝ}
    (hpu : p < u) (hur : u < r) (hu : α.val u < α.val r) :
    (∫ s in p..r, α.val s-α.val r) < 0 := by
  have hh : 0 < ∫ s in p..r, α.val r-α.val s := by
    apply intervalIntegral_pos_of_interior_interval le_rfl hpu hur.le
      (intervalIntegrable_const.sub α.property.2.intervalIntegrable)
    · intro s hs
      exact sub_nonneg.mpr (α.property.2 hs.2.le)
    · intro s hs
      exact sub_pos.mpr ((α.property.2 hs.2.le).trans_lt hu)
  have he : (fun s => α.val r-α.val s) = fun s => -(α.val s-α.val r) := by
    funext s; ring
  rw [he,intervalIntegral.integral_neg] at hh
  linarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m T : ℝ} (hm : 0 < m) (hT : 0 ≤ T)

include hT

theorem scalarProfileGap_zero : (scalarProfileHeatJet α hα l t).filledSquare hm T 0 0 = 0 := by
  let J := scalarProfileHeatJet α hα l t
  have ho := scalarClockProfileJet_parity α hα l t hm (Real.toNNReal T) 1 0
  have he : (Real.toNNReal T:ℝ) = T := Real.coe_toNNReal _ hT
  simp only [scalarClockProfileJet,neg_zero,pow_one,neg_one_mul] at ho
  rw [he] at ho
  have hz : J.scalarClockJet m 1 T 0 = 0 := by
    change J.scalarClockJet m 1 T 0 = -J.scalarClockJet m 1 T 0 at ho
    linarith
  rw [J.scalarClockJet_one hm] at hz
  rw [J.filledSquare_zero]
  change (clockTest m J.F (J.G 0) T 0)^2 = 0
  change (clockTest m J.F (J.G 0) T 0) = 0 at hz
  rw [hz,zero_pow (by norm_num : 2 ≠ 0)]

omit hT in
theorem scalarProfileGap_energy_zero :
    (scalarProfileHeatJet α hα l t).scalarGapEnergy m T 0 0 =
      ((scalarProfileHeatJet α hα l t).scalarClockJet m 2 T 0)^2 := by
  simp only [HeatJet.scalarGapEnergy,sub_zero,clockTest_zero]

end

 

theorem scalarProfileGap_strict_balance (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {m T : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (hT : 0 < T)
    (harea : 2*(∫ s in 0..T, (scalarProfileHeatJet α hα l t).filledSquare hm T s 0) =
      T*(scalarProfileHeatJet α hα l t).filledSquare hm T T 0) :
    (scalarProfileHeatJet α hα l t).filledSquare hm T T 0 <
      T*((scalarProfileHeatJet α hα l t).scalarClockJet m 2 T 0)^2 := by
  let J := scalarProfileHeatJet α hα l t
  have hG (k : ℕ) (i : Fin 1) : BddSmooth k (J.G i) := scalarProfileJet_bddSmooth_all α hα l t k 0
  have hH (k : ℕ) (i : Fin 1) : BddSmooth k (J.H i) := scalarProfileJet_bddSmooth_all α hα l t k 1
  have hh := gap_strict_balance hT (J.continuous_filledSquare hm T 0).continuousOn
    (J.continuous_scalarGapEnergy hG hm T 0).continuousOn
    (J.continuous_scalarGapCurvature hG hm T 0).continuousOn
    (fun s hs => scalarProfileGap_hasDerivAt α hα l t hm hs)
    (fun s hs => scalarProfileGapEnergy_hasDerivAt α hα l t hm hs)
    (J.continuous_scalarGapCurvature hG hm T 0).continuousAt
    (fun s hs => J.hasDerivAt_scalarGapCurvature hG hm hH hs 0)
    (fun s hs hz => scalarProfileGapCurvature_root hα l t hm hmα hs hz)
    (scalarProfileGap_initial_curvature α hα l t hm (hmα.trans (hα l)) hT.le)
    (scalarProfileGap_zero α hα l t hm hT.le) harea
  rw [scalarProfileGap_energy_zero α hα l t] at hh
  exact hh
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarMinimizer_gap_cumulative {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    ∀ s ∈ Ioc (0:ℝ) (T*q),
      (∫ r in 0..s, (scalarTailJet hT α q).filledSquare hm (T*q) r 0) ≤ (1/T)*s^2/2 := by
  intro s hs
  have hp : 0 < s/T := div_pos hs.1 hT
  have hpq : s/T ≤ q := (div_le_iff₀ hT).mpr (by nlinarith [hs.2])
  have hh := scalarMinimizer_prefix_integral hT hp hpq hq.2 α hα hm hm1 hf hmin
  have he : T*(s/T)=s := by field_simp
  rw [he] at hh
  have ha : T*(s/T)^2/2 = (1/T)*s^2/2 := by field_simp
  rw [← ha]
  linarith

theorem scalarMinimizer_gap_initial_slope {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    ((scalarTailJet hT α q).scalarClockJet m 2 (T*q) 0)^2 ≤ 1/T := by
  let J := scalarTailJet hT α q
  have hh := cumulative_initial_slope (mul_pos hT hq.1)
    (J.continuous_filledSquare hm (T*q) 0)
    ((J.continuous_scalarGapEnergy (scalarTailJet_G_smooth hT α q) hm (T*q) 0).continuousAt)
    (scalarProfileGap_zero (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*q) (Real.toNNReal (T*(1-q))) hm (mul_nonneg hT.le hq.1.le))
    (fun s hs => scalarProfileGap_hasDerivAt (rescaledMassProfile α hT)
      (fun r => (α.property.1 (r/T)).2) (T*q) (Real.toNNReal (T*(1-q))) hm hs)
    (scalarMinimizer_gap_cumulative hT hq α hα hm hm1 hf hmin)
  simp only [HeatJet.scalarGapEnergy, sub_zero, clockTest_zero] at hh
  exact hh

theorem scalarMinimizer_gap_endpoint {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioo (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hrise : ∀ r ∈ Ioc q 1, m < α.val r)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (scalarTailJet hT α q).filledSquare hm (T*q) (T*q) 0 = q := by
  have ha := scalarMinimizer_head_balance hT hq α hα hm hm1 hf hrise hmin
  have hai : (∫ r in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) r 0) = (1/T)*(T*q)^2/2 := by
    have he : (1/T)*(T*q)^2/2 = T*q^2/2 := by field_simp
    rw [he]
    linarith
  have hl := cumulative_endpoint (mul_pos hT hq.1)
    ((scalarTailJet hT α q).continuous_filledSquare hm (T*q) 0)
    (scalarMinimizer_gap_cumulative hT ⟨hq.1,hq.2.le⟩ α hα hm hm1 hf hmin) hai
  have hqeq : (1/T)*(T*q)=q := by field_simp
  rw [hqeq] at hl
  have hu := scalarMinimizer_endpoint_le hT hq α hα hm hm1.le hf
    (fun r hr => hrise r ⟨hr.1,hr.2.le⟩) hmin
  have he : (scalarTailJet hT α q).filledSquare hm (T*q) (T*q) 0 =
      (scalarTailJet hT α q).observedSquare m (T*q) 0 := by
    rw [HeatJet.filledSquare_terminal]
    rfl
  exact le_antisymm (he.trans_le hu) hl

 

theorem scalarMinimizer_no_isolated_origin {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioo (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hrise : ∀ r ∈ Ioc q 1, m < α.val r)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) : False := by
  have hmq : m ≤ α.val q := by
    rw [← hf 0 ⟨le_rfl,hq.1⟩]
    exact α.property.2 hq.1.le
  have hend := scalarMinimizer_gap_endpoint hT hq α hα hm hm1 hf hrise hmin
  have harea := scalarMinimizer_head_balance hT hq α hα hm hm1 hf hrise hmin
  have hslope := scalarMinimizer_gap_initial_slope hT ⟨hq.1,hq.2.le⟩ α hα hm hm1 hf hmin
  have hma : m ≤ (rescaledMassProfile α hT).mass (T*q) := by
    simpa only [rescaledMassProfile,mul_div_cancel_left₀ _ hT.ne'] using hmq
  have hstrict := scalarProfileGap_strict_balance (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) hm hma
    (mul_pos hT hq.1) (by
      change 2*(∫ s in 0..T*q, (scalarTailJet hT α q).filledSquare hm (T*q) s 0) =
        T*q*(scalarTailJet hT α q).filledSquare hm (T*q) (T*q) 0
      rw [hend,harea]
      ring)
  change (scalarTailJet hT α q).filledSquare hm (T*q) (T*q) 0 <
    T*q*((scalarTailJet hT α q).scalarClockJet m 2 (T*q) 0)^2 at hstrict
  rw [hend] at hstrict
  have hh := mul_le_mul_of_nonneg_left hslope (mul_nonneg hT.le hq.1.le)
  have he : T*q*(1/T) = q := by field_simp
  rw [he] at hh
  exact not_lt_of_ge hh hstrict

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarMinimizer_head_balance_one {T m : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hf : ∀ r ∈ Ico (0:ℝ) 1, α.val r = m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    2*(∫ s in 0..T, (scalarTailJet hT α 1).filledSquare hm T s 0) = T := by
  let D := (1/2:ℝ)*(∫ s in 0..T, (scalarTailJet hT α 1).filledSquare hm T s 0)-T/4
  have hdu := scalarMinimizer_head_derivative_nonpos hT (show (1:ℝ) ∈ Ioc 0 1 by simp)
    α hα hm hm1 hf hmin
  simp only [mul_one,one_pow] at hdu
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp
    (scalarHeadValue_hasDerivAt hT (show (0:ℝ) ≤ 1 by norm_num) α hm hm1)).2
  simp only [mul_one,one_pow] at hd
  have hdl : 0 ≤ D := by
    apply ge_of_tendsto hd
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ b : ℝ in 𝓝[>] m, b < 1 from
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hm1))] with b hmb hb1
    have hb := hm.trans hmb
    let β := floorMassProfile α hb.le hb1.le
    have hβ := floorMassProfile_mem hα hb.le hb1.le
    have hdiff := scalarParisiValue_head_error hT (show (0:ℝ) < 1 by norm_num)
      (q:=1) (r:=1) le_rfl le_rfl α β hm hb hf
      (fun s hs => floorMassProfile_head α hb.le hb1.le hmb.le hf hs)
      (d:=b-m) (fun s hs => False.elim (not_lt_of_ge hs.1.le hs.2))
      (fun s hs => False.elim (not_lt_of_ge hs.1.le hs.2))
    simp only [sub_self,mul_zero] at hdiff
    have hdiff' := (abs_le.mp hdiff).2
    have hminβ := hmin β hβ
    rw [slope_def_field]
    apply div_nonneg _ (sub_pos.mpr hmb).le
    linarith
  dsimp [D] at hdl
  linarith

theorem scalarTailJet_filledSquare_le_one {T q m : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hm : 0 < m) :
    (scalarTailJet hT α q).filledSquare hm (T*q) (T*q) 0 ≤ 1 := by
  rw [HeatJet.filledSquare_terminal]
  have hh := clockTest_abs_le (scalarTailJet hT α q).lipschitz
    (scalarTailJet hT α q).square.smoothA
    (scalarTailJet_square_bound hT α q) m (T*q) 0
  exact (le_abs_self _).trans hh

 

theorem scalarMinimizer_no_isolated_origin_Ioc {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hm : 0 < m) (hm1 : m < 1) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hrise : ∀ r ∈ Ioc q 1, m < α.val r)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) : False := by
  obtain hq1 | hq1 := hq.2.lt_or_eq
  · exact scalarMinimizer_no_isolated_origin hT ⟨hq.1,hq1⟩ α hα hm hm1 hf hrise hmin
  subst q
  have harea := scalarMinimizer_head_balance_one hT α hα hm hm1 hf hmin
  have hslope := scalarMinimizer_gap_initial_slope hT hq α hα hm hm1 hf hmin
  simp only [mul_one] at hslope
  have ha : (∫ s in 0..T, (scalarTailJet hT α 1).filledSquare hm T s 0) = (1/T)*T^2/2 := by
    have he : (1/T)*T^2/2 = T/2 := by field_simp
    rw [he]
    linarith
  have hc := scalarMinimizer_gap_cumulative hT hq α hα hm hm1 hf hmin
  simp only [mul_one] at hc
  have hl := cumulative_endpoint hT ((scalarTailJet hT α 1).continuous_filledSquare hm T 0) hc ha
  have hmul : (1/T)*T = 1 := by field_simp
  rw [hmul] at hl
  have hu := scalarTailJet_filledSquare_le_one hT (q:=1) α hm
  simp only [mul_one] at hu
  have hend := le_antisymm hu hl
  have hmq : m ≤ α.val 1 := by
    rw [← hf 0 ⟨le_rfl,zero_lt_one⟩]
    exact α.property.2 zero_le_one
  have hma : m ≤ (rescaledMassProfile α hT).mass T := by
    simpa only [rescaledMassProfile,div_self hT.ne'] using hmq
  have hstrict := scalarProfileGap_strict_balance (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (T*1) (Real.toNNReal (T*(1-1))) hm (by simpa only [mul_one] using hma) hT (by
      change 2*(∫ s in 0..T, (scalarTailJet hT α 1).filledSquare hm T s 0) =
        T*(scalarTailJet hT α 1).filledSquare hm T T 0
      rw [harea,hend,mul_one])
  change (scalarTailJet hT α 1).filledSquare hm T T 0 <
    T*((scalarTailJet hT α 1).scalarClockJet m 2 T 0)^2 at hstrict
  rw [hend] at hstrict
  have hh := mul_le_mul_of_nonneg_left hslope hT.le
  have he : T*(1/T)=1 := by field_simp
  rw [he] at hh
  exact not_lt_of_ge hh hstrict

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

 

theorem scalar_first_rise {q m : ℝ} (hq : 0 < q)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles) (hm1 : m < 1)
    (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m) :
    ∃ p ∈ Ioc (0:ℝ) 1, (∀ r ∈ Ico (0:ℝ) p, α.val r = m) ∧
      ∀ r ∈ Ioc p 1, m < α.val r := by
  let S := {r : ℝ | m < α.val r}
  have h0 : α.val 0 = m := hf 0 ⟨le_rfl,hq⟩
  have hS : S.Nonempty := ⟨2,by simpa only [S,mem_ofPred_eq,hα.2 2 (by norm_num)] using hm1⟩
  have hqS : ∀ r ∈ S, q ≤ r := by
    intro r hr
    by_contra hn
    have hrq : r < q := lt_of_not_ge hn
    by_cases hr0 : r < 0
    · have hl := α.property.2 hr0.le
      rw [h0] at hl
      exact not_lt_of_ge hl hr
    · have he := hf r ⟨le_of_not_gt hr0,hrq⟩
      change m < α.val r at hr
      rw [he] at hr
      exact lt_irrefl _ hr
  have hb : BddBelow S := ⟨q,hqS⟩
  let p := sInf S
  have hqp : q ≤ p := le_csInf hS hqS
  have hp : 0 < p := hq.trans_le hqp
  have hp1 : p ≤ 1 := by
    by_contra hn
    have h1p : 1 < p := lt_of_not_ge hn
    let r := (1+p)/2
    have hr : 1 < r := by dsimp [r]; linarith
    have hrS : r ∈ S := by change m < α.val r; rw [hα.2 r hr]; exact hm1
    have hh : p ≤ r := csInf_le hb hrS
    dsimp [r] at hh
    linarith
  refine ⟨p,⟨hp,hp1⟩,?_,?_⟩
  · intro r hr
    apply le_antisymm
    · by_contra hn
      have hrS : r ∈ S := lt_of_not_ge hn
      exact not_lt_of_ge (csInf_le hb hrS) hr.2
    · rw [← h0]
      exact α.property.2 hr.1
  · intro r hr
    obtain ⟨s,hs,hsr⟩ := exists_lt_of_csInf_lt hS hr.1
    exact hs.trans_le (α.property.2 hsr.le)

 

theorem scalarMinimizer_no_positive_plateau {T q m : ℝ} (hT : 1 < T) (hq : 0 < q)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles) (hm : 0 < m)
    (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = m)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) α ≤
      scalarParisiValue (by linarith : 0 < T) β) : False := by
  have hm1 : m ≤ 1 := by rw [← hf 0 ⟨le_rfl,hq⟩]; exact (α.property.1 0).2
  obtain hm1 | hm1 := hm1.lt_or_eq
  · obtain ⟨p,hp,hfp,hrise⟩ := scalar_first_rise hq α hα hm1 hf
    exact scalarMinimizer_no_isolated_origin_Ioc (by linarith) hp α hα hm hm1 hfp hrise hmin
  · have he : α = diracMassProfile 0 := by
      apply Subtype.ext
      funext r
      change α.val r = if r < 0 then 0 else 1
      by_cases hr : r < 0
      · rw [ite_eq_left hr,hα.1 r hr]
      · rw [ite_eq_right hr]
        apply le_antisymm (α.property.1 r).2
        rw [← hm1,← hf 0 ⟨le_rfl,hq⟩]
        exact α.property.2 (le_of_not_gt hr)
    subst α
    exact scalarParisi_no_dirac_minimizer hT (show (0:ℝ) ∈ Icc 0 1 by simp) hmin

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

 

theorem scalarMinimizer_origin_atom_accumulates {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) α ≤
      scalarParisiValue (by linarith : 0 < T) β)
    (hAtom : 0 < (profileStieltjes α).measure {(0:ℝ)}) {q : ℝ} (hq : 0 < q) :
    0 < (profileStieltjes α).measure (Ioo 0 q) := by
  by_contra hn
  have hz : (profileStieltjes α).measure (Ioo 0 q) = 0 := le_zero_iff.mp (le_of_not_gt hn)
  let β := rightMassProfile α
  have hβ : β ∈ scalarProfiles := rightMassProfile_mem hα
  have hm : 0 < β.val 0 := by
    rw [(profileStieltjes α).measure_singleton,profileStieltjes_left_zero hα,sub_zero] at hAtom
    exact ENNReal.ofReal_pos.mp hAtom
  have hf : ∀ r ∈ Ico (0:ℝ) q, β.val r = β.val 0 := by
    intro r hr
    have hi : Ioc (0:ℝ) r ⊆ Ioo 0 q := fun s hs => ⟨hs.1,hs.2.trans_lt hr.2⟩
    have hz' : (profileStieltjes α).measure (Ioc 0 r) = 0 :=
      le_zero_iff.mp ((measure_mono hi).trans_eq hz)
    rw [(profileStieltjes α).measure_Ioc] at hz'
    have hl : β.val r-β.val 0 ≤ 0 := ENNReal.ofReal_eq_zero.mp hz'
    exact le_antisymm (by linarith) (β.property.2 hr.1)
  have hminβ : ∀ γ ∈ scalarProfiles, scalarParisiValue (by linarith : 0 < T) β ≤
      scalarParisiValue (by linarith : 0 < T) γ := by
    intro γ hγ
    rw [scalarParisiValue_congr_ae (by linarith) (rightMassProfile_ae α)]
    exact hmin γ hγ
  exact scalarMinimizer_no_positive_plateau hT hq β hβ hm hf hminβ

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.potential_zero_mass_difference {n : ℕ} (J : HeatJet n)
    (D : Fin (n+1) → ℝ) (hD : ∀ i x, |J.G i x| ≤ D i)
    {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) (x : Fin (n+1) → ℝ) :
    |clockContinuation m J.F t x-clockRoot J.F t x| ≤ m/2*(∑ i, (D i)^2)*t := by
  have hp := shiftedContinuation_tendsto_zero_mass J.lipschitz
    (exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal t)) x
  change Tendsto (fun a : ℝ => clockContinuation a J.F t x) (𝓝[>] 0)
    (𝓝 (clockRoot J.F t x)) at hp
  have hb : Tendsto (fun a : ℝ => |m-a|/2*(∑ i, (D i)^2)*t) (𝓝[>] 0)
      (𝓝 (m/2*(∑ i, (D i)^2)*t)) := by
    simpa only [Pi.sub_apply,id_eq,sub_zero,abs_of_pos hm] using
      ((((continuousAt_const : ContinuousAt (fun _ : ℝ => m) 0).sub continuousAt_id).abs.div_const 2).mul_const
        (∑ i, (D i)^2) |>.mul_const t).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub hp).abs) hb
    (by filter_upwards [self_mem_nhdsWithin] with a ha
        exact J.potential_mass_difference D hD hm ha ht x)

theorem HeatJet.nonnegativeProfileValue_zero {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (ht : 0 < (t:ℝ))
    (hf : ∀ s ∈ Ico l (l+t), α.mass s = 0) (x : Fin (n+1) → ℝ) :
    J.nonnegativeProfileValue α l t x = clockRoot J.F t x := by
  have he (k : ℕ) : 0 < (1/2:ℝ)^k := by positivity
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num) (by norm_num),Eventually.of_forall he⟩
  have hh := (shiftedContinuation_tendsto_zero_mass J.lipschitz
    (exponentialIncrement_gaussian (fun _ : Fin (n+1) => t)) x).comp hp
  have hhh : Tendsto (fun k : ℕ => clockContinuation ((1/2:ℝ)^k) J.F t x) atTop
      (𝓝 (clockRoot J.F t x)) := by
    simpa only [clockContinuation,clockRoot,Real.toNNReal_coe,Function.comp_def] using hh
  have heq (k : ℕ) : J.profileValue (α.positiveApprox k) l t x =
      clockContinuation ((1/2:ℝ)^k) J.F t x := by
    apply J.profileValue_constant (α.positiveApprox k) (he k) l t ht
    intro s hs
    change α.mass s+(1/2:ℝ)^k = _
    rw [hf s hs,zero_add]
  simp_rw [← heq] at hhh
  exact tendsto_nhds_unique (J.regularized_tendsto α l t x) hhh

theorem scalarProfile_zero_head (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) {s : ℝ≥0} (hs : 0 < (s:ℝ)) (t : ℝ≥0)
    (hf : ∀ r ∈ Ico l (l+s), α.mass r = 0) (x : Fin 1 → ℝ) :
    scalarTerminal.nonnegativeProfileValue α l (s+t) x =
      clockRoot (scalarProfileHeatJet α hα (l+s) t).F s x := by
  rw [scalarProfile_concat α hα]
  exact HeatJet.nonnegativeProfileValue_zero _ α l s hs hf x

theorem scalarParisiValue_zero_head {T q : ℝ} (hT : 0 < T) (hq : q ∈ Ioc (0:ℝ) 1)
    (α : boundedMassProfiles) (hf : ∀ r ∈ Ico (0:ℝ) q, α.val r = 0) :
    scalarParisiValue hT α = clockRoot (scalarTailJet hT α q).F (T*q) 0-
      T/2*scalarPenalty α-T/4 := by
  have hs : 0 < T*q := mul_pos hT hq.1
  have ht : 0 ≤ T*(1-q) := mul_nonneg hT.le (sub_nonneg.mpr hq.2)
  have he : Real.toNNReal (T*q)+Real.toNNReal (T*(1-q)) = (⟨T,hT.le⟩:ℝ≥0) := by
    apply NNReal.eq
    change ((Real.toNNReal (T*q):ℝ)+(Real.toNNReal (T*(1-q)):ℝ)) = T
    rw [Real.coe_toNNReal _ hs.le,Real.coe_toNNReal _ ht]
    ring
  have hh := scalarProfile_zero_head (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) 0
    (s:=Real.toNNReal (T*q)) (by rwa [Real.coe_toNNReal _ hs.le])
    (Real.toNNReal (T*(1-q))) (by
      intro r hr
      change α.val (r/T) = 0
      apply hf
      simp only [zero_add,Real.coe_toNNReal _ hs.le] at hr
      exact ⟨div_nonneg hr.1 hT.le,(div_lt_iff₀ hT).mpr (by nlinarith [hr.2])⟩) 0
  rw [he] at hh
  simp only [zero_add,Real.coe_toNNReal _ hs.le] at hh
  unfold scalarParisiValue
  rw [hh]
  rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

section
variable {J : HeatJet 0} (hJ : J.ScalarAdmissible) (hA : J.GradientTest)
include hJ hA

theorem HeatJet.gradient_test_bounds :
    (∀ y, |J.A y| ≤ 1) ∧ (∀ i y, |J.G i y| ≤ 1) ∧ (∀ i y, |J.A₁ i y| ≤ 1) := by
  refine ⟨?_,?_,?_⟩
  · intro y; rw [hA.1]; exact hJ.gradient y
  · intro i y; rw [Fin.eq_zero i]; exact hJ.gradient y
  · intro i y; rw [hA.2 i,Fin.eq_zero i,abs_of_nonneg (hJ y).1]; exact hJ.curvature y

theorem HeatJet.gradient_mass_zero_bound {b t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (x : Fin 1 → ℝ) :
    |clockTest b J.F J.A t x-clockRoot J.A t x| ≤ 4*b*t := by
  obtain ⟨hAt,hGt,hDt⟩ := HeatJet.gradient_test_bounds hJ hA
  have hh := J.clock_mass_difference (fun _ => 1) (by norm_num : (0:ℝ) ≤ 1)
    (by norm_num : (0:ℝ) ≤ 1) (fun _ => by norm_num) hAt hGt
    (by simpa only [one_mul] using hDt) (a:=0) le_rfl zero_le_one hb hb1 ht x
  rw [clockTest_zero_mass,abs_sub_comm] at hh
  norm_num only [zero_sub,abs_neg,abs_of_pos hb,Fin.sum_univ_one,one_pow,mul_one] at hh
  nlinarith

theorem HeatJet.gradient_square_mass_zero_bound {b t : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (x : Fin 1 → ℝ) :
    |clockTest b J.F J.square.A t x-clockRoot J.square.A t x| ≤ 5*b*t := by
  obtain ⟨hAt,hGt,hDt⟩ := HeatJet.gradient_test_bounds hJ hA
  have hSq (y) : |J.square.A y| ≤ 1 := by
    change |(J.A y)^2| ≤ 1
    rw [abs_pow]
    nlinarith [hAt y,abs_nonneg (J.A y)]
  have hSqD (i) (y) : |J.square.A₁ i y| ≤ (2:ℝ)*1*1 := by
    change |2*(J.A y*J.A₁ i y)| ≤ _
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [mul_le_mul (hAt y) (hDt i y) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)]
  have hh := J.square.clock_mass_difference (fun _ => 1) (by norm_num : (0:ℝ) ≤ 1)
    (by norm_num : (0:ℝ) ≤ 2) (fun _ => by norm_num) hSq hGt hSqD
    (a:=0) le_rfl zero_le_one hb hb1 ht x
  rw [clockTest_zero_mass,abs_sub_comm] at hh
  norm_num only [zero_sub,abs_neg,abs_of_pos hb,Fin.sum_univ_one,one_pow,mul_one] at hh
  change |clockTest b J.F J.square.A t x-clockRoot J.square.A t x| ≤ _ at hh
  nlinarith

omit hJ in
theorem HeatJet.massEnergy_eq_mixedSquare (a : ℝ) {b : ℝ} (hb : 0 < b)
    (T s : ℝ) (x : Fin 1 → ℝ) : J.massEnergy a hb T s x = J.mixedSquare a hb T s x := by
  unfold HeatJet.massEnergy HeatJet.mixedSquare HeatJet.potentialEnergy
  congr 1
  funext y
  rw [Fin.sum_univ_one,← (hA.evolve hb (T-s)).1]
  rfl

theorem HeatJet.massEnergy_outer_zero_bound {a b T s : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hs : 0 ≤ s) (x : Fin 1 → ℝ) :
    |J.massEnergy a hb T s x-J.massEnergy 0 hb T s x| ≤ 5*a*s := by
  rw [HeatJet.massEnergy_eq_mixedSquare hA,HeatJet.massEnergy_eq_mixedSquare hA]
  unfold HeatJet.mixedSquare
  rw [clockTest_zero_mass]
  exact HeatJet.gradient_square_mass_zero_bound (hJ.evolve hb hb1 (T-s))
    (hA.evolve hb (T-s)) ha ha1 hs x

theorem HeatJet.massEnergy_integral_zero_tendsto {b T : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hT : 0 ≤ T) (x : Fin 1 → ℝ) :
    Tendsto (fun a => ∫ s in 0..T, J.massEnergy a hb T s x) (𝓝[>] 0)
      (𝓝 (∫ s in 0..T, J.massEnergy 0 hb T s x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ a : ℝ in 𝓝 0, a < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds] with a ha ha1
    exact ⟨ha,ha1.le⟩
  have hbound : ∀ᶠ a : ℝ in 𝓝[>] 0,
      dist (∫ s in 0..T, J.massEnergy a hb T s x) (∫ s in 0..T, J.massEnergy 0 hb T s x) ≤
        5*a*T*T := by
    filter_upwards [he] with a ha
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=0) (b:=T) (C:=5*a*T)
      (f:=fun s => J.massEnergy a hb T s x-J.massEnergy 0 hb T s x) (fun s hs => by
        rw [uIoc_of_le hT] at hs
        exact (HeatJet.massEnergy_outer_zero_bound hJ hA ha.1 ha.2 hb hb1 hs.1.le x).trans
          (mul_le_mul_of_nonneg_left hs.2 (mul_nonneg (by norm_num) ha.1.le)))
    rw [intervalIntegral.integral_sub ((J.continuous_massEnergy a hb T x).intervalIntegrable 0 T)
      ((J.continuous_massEnergy 0 hb T x).intervalIntegrable 0 T)] at hh
    simpa only [Real.norm_eq_abs,Real.dist_eq,sub_zero,abs_of_nonneg hT] using hh
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound
  simpa only [id_eq,mul_zero,zero_mul] using
    ((((continuous_id.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds).const_mul 5).mul_const T |>.mul_const T)

end
end SKFluctuations.Hierarchy

end

end OAI
