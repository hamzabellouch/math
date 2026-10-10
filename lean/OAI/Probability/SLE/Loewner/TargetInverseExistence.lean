import OAI.Probability.SLE.Angle.TargetPositiveFlow
import OAI.Probability.SLE.Loewner.TargetInverseMeasurability

namespace OAI

/-! Reverse flow supplies every point of the upper half-plane as an
image of the raw surviving flow, for every continuous based driver. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric Complex
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma reverseField_im_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) :
    0 ≤ (reverseField a u z).im := by
  have hm : 0 ≤ max a z.im := ha.le.trans (le_max_left _ _)
  have hd : 0 ≤ Complex.normSq (reverseCenter a u z) := Complex.normSq_nonneg _
  have he : (reverseField a u z).im=2*(max a z.im / Complex.normSq (reverseCenter a u z)) := by
    simp [reverseField,Complex.mul_im,Complex.inv_im,reverseCenter_im]
    ring
  rw [he]
  exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (div_nonneg hm hd)

namespace Target

theorem reverse_trajectory_preimage
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (T : ℝ≥0) (w : ℂ)
    (η : ℝ) (hη : 0 < η) (hηw : η ≤ w.im) (Q : ℝ → ℂ)
    (hQ0 : Q 0=w)
    (hQd : ∀ s, 0 ≤ s → HasDerivWithinAt Q
      (reverseField η (driverValue b ((T:ℝ)-κ*s)) (Q s)) (Ici 0) s) :
    Surviving κ b (Q ((T:ℝ)/κ)) T ∧ flow κ b (Q ((T:ℝ)/κ)) T=w := by
  have hQc : ContinuousOn Q (Ici 0) :=
    fun s hs => (hQd s hs).continuousWithinAt
  have hQi : MonotoneOn (fun s => (Q s).im) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (Complex.continuous_im.comp_continuousOn hQc)
      (fun s hs => (Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt s (hQd s (interior_subset hs))).mono interior_subset)
    intro s hs
    exact reverseField_im_nonneg hη _ _
  have hheightQ (s : ℝ) (hs : 0 ≤ s) : w.im ≤ (Q s).im := by
    simpa only [hQ0] using hQi (show (0:ℝ) ∈ Ici (0:ℝ) from le_refl (0:ℝ)) hs hs
  let Y (s : ℝ) := Q (((T:ℝ)-s)/κ)
  let z := Y 0
  have hmaps : MapsTo (fun s : ℝ => ((T:ℝ)-s)/κ) (Icc 0 (T:ℝ)) (Ici 0) :=
    fun s hs => div_nonneg (sub_nonneg.mpr hs.2) hκ.le
  have hY : ContinuousOn Y (Icc 0 (T:ℝ)) :=
    hQc.comp ((continuous_const.sub continuous_id).div_const κ).continuousOn hmaps
  have hYheight : ∀ s ∈ Icc 0 (T:ℝ), w.im ≤ (Y s).im :=
    fun s hs => hheightQ _ (hmaps hs)
  have hYd (s : ℝ) (hs : s ∈ Ico 0 (T:ℝ)) :
      HasDerivWithinAt Y ((a κ:ℂ)/(Y s-driverValue b s)) (Ici s) s := by
    have ht : 0 ≤ ((T:ℝ)-s)/κ := hmaps (Ico_subset_Icc_self hs)
    have hi : HasDerivWithinAt (fun r : ℝ => ((T:ℝ)-r)/κ) (-1/κ) (Icc 0 (T:ℝ)) s := by
      convert (((hasDerivAt_id s).const_sub (T:ℝ)).div_const κ).hasDerivWithinAt using 1
      simp
    have hd := (hQd _ ht).scomp s hi hmaps
    have he : (T:ℝ)-κ*(((T:ℝ)-s)/κ)=s := by field_simp [hκ.ne']; ring
    have hh : η ≤ (Y s).im := hηw.trans (hYheight s (Ico_subset_Icc_self hs))
    have hc : (-1/κ) • reverseField η (driverValue b ((T:ℝ)-κ*(((T:ℝ)-s)/κ))) (Y s) =
        (a κ:ℂ)/(Y s-driverValue b s) := by
      have hUt : driverValue b ((T:ℝ)-κ*(((T:ℝ)-s)/κ))=driverValue b s := by rw [he]
      rw [hUt,reverseField,reverseCenter_eq hh]
      simp only [Complex.real_smul,a,div_eq_mul_inv]
      push_cast
      ring
    exact hasDerivWithinAt_Ici_of_Icc hs (hd.congr_deriv hc)
  obtain ⟨hz,hflow⟩ := flow_eq_of_positive_trajectory κ b z T T.coe_nonneg Y hY rfl
    w.im (hη.trans_le hηw) hYheight hYd
  constructor
  · simpa only [z,Y,sub_zero] using hz
  · simpa only [z,Y,sub_zero,sub_self,zero_div,hQ0] using hflow

theorem exists_surviving_preimage
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (T : ℝ≥0) (w : ℂ)
    (hw : w ∈ upperHalfPlane) :
    ∃ z, Surviving κ b z T ∧ flow κ b z T=w := by
  let η := w.im/2
  have hη : 0 < η := half_pos hw
  let U (s : ℝ) (_ : Unit) := driverValue b ((T:ℝ)-κ*s)
  have hUc : Continuous (fun s : ℝ => U s ()) := by
    exact b.continuous.comp (continuous_real_toNNReal.comp
      (continuous_const.sub (continuous_const.mul continuous_id)))
  have hUm : Measurable (fun q : ℝ × Unit => U q.1 q.2) :=
    hUc.measurable.comp measurable_fst
  obtain ⟨Q,hQm,hQ0,hQd⟩ := exists_measurable_reverse_flow U hUm
    (fun _ => hUc) (fun _ => w) measurable_const hη
  exact ⟨Q ((T:ℝ)/κ) (), reverse_trajectory_preimage κ hκ b T w η hη
    (half_le_self (show 0 ≤ w.im from hw.le)) (fun s => Q s ()) (hQ0 ()) (hQd ())⟩

end Target
end SLEExactGauge

end

end OAI
