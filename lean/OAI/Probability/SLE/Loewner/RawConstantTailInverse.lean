import OAI.Probability.SLE.Loewner.RawSurvivingDerivative
import OAI.Probability.SLE.Loewner.RawSurvivingMonotone
import OAI.Probability.SLE.Loewner.SlitTimeGluing
import OAI.Probability.SLE.Loewner.LinearReverseTrajectory

namespace OAI

/-! The inverse after a constant-driver tail is the translated vertical
inverse followed by the inverse at the joining time. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem inverseFlow_constant_tail (b : Driver) (A S : ℝ≥0) (u : ℝ)
    (hb : ∀ t : ℝ≥0, A ≤ t → b t=u) {w : ℂ} (hw : w∈upperHalfPlane) :
    inverseFlow 1 b (A+S) w=
      inverseFlow 1 b A ((u:ℂ)+inverseFlow 1 (linearDriver 0) S (w-(u:ℂ))) := by
  let c := linearDriver 0
  let v := inverseFlow 1 c S (w-(u:ℂ))
  have hw' : w-(u:ℂ)∈upperHalfPlane := by simpa [upperHalfPlane] using hw
  have hvS : Surviving 1 c v S := inverseFlow_surviving 1 (by norm_num) c S _ hw'
  have hvH : v∈upperHalfPlane := surviving_mem_upperHalfPlane 1 c v S S.coe_nonneg hvS
  have hvend : flow 1 c v S=w-(u:ℂ) := flow_inverseFlow 1 (by norm_num) c S _ hw'
  let z := inverseFlow 1 b A ((u:ℂ)+v)
  have hqH : (u:ℂ)+v∈upperHalfPlane := by simpa [upperHalfPlane] using hvH
  have hzA : Surviving 1 b z A := inverseFlow_surviving 1 (by norm_num) b A _ hqH
  have hzH : z∈upperHalfPlane := surviving_mem_upperHalfPlane 1 b z A A.coe_nonneg hzA
  have hzjoin : flow 1 b z A=(u:ℂ)+v := flow_inverseFlow 1 (by norm_num) b A _ hqH
  let f := flow 1 b z
  let g := fun t : ℝ => (u:ℂ)+flow 1 c v (t-(A:ℝ))
  let Y := fun t : ℝ => if t ≤ (A:ℝ) then f t else g t
  have hjoin : f A=g A := by
    dsimp [f,g]
    rw [sub_self,flow_zero 1 c v hvH]
    exact hzjoin
  have hleft (t : ℝ) (ht : t ≤ A) : Y t=f t := ite_eq_left ht
  have hright (t : ℝ) (ht : A ≤ t) : Y t=g t := by
    by_cases ht' : t ≤ A
    · have he : t=A := le_antisymm ht' ht
      simpa only [he,Y,ite_eq_left le_rfl] using hjoin
    · exact ite_eq_right ht'
  have hd (t : ℝ) (ht : t∈Icc 0 ((A+S:ℝ≥0):ℝ)) :
      HasDerivWithinAt Y (2/(Y t-(b t.toNNReal:ℂ))) (Ici 0) t := by
    apply hasDerivWithinAt_time_splice f g A t _ hjoin
    · intro htA
      have hs := surviving_of_le_time 1 b z ht.1 htA hzA
      have hh := flow_hasDerivWithinAt_of_survival b z ht.1 hs
      simpa only [←hleft t htA,f] using hh
    · intro hAt
      have hts : 0 ≤ t-(A:ℝ) := sub_nonneg.mpr hAt
      have htsS : t-(A:ℝ) ≤ S := by
        have hh : t ≤ (A:ℝ)+(S:ℝ) := by simpa only [NNReal.coe_add] using ht.2
        linarith
      have hs := surviving_of_le_time 1 c v hts htsS hvS
      have hh := flow_hasDerivWithinAt_of_survival c v hts hs
      have hlin : HasDerivWithinAt (fun t : ℝ => t-(A:ℝ)) 1 (Ici (A:ℝ)) t :=
        ((hasDerivAt_id t).sub_const (A:ℝ)).hasDerivWithinAt
      have hm : MapsTo (fun t : ℝ => t-(A:ℝ)) (Ici (A:ℝ)) (Ici 0) :=
        fun t ht => show 0 ≤ t-(A:ℝ) from sub_nonneg.mpr ht
      have hh' := (hh.scomp t hlin hm).const_add (u:ℂ)
      have hbt : b t.toNNReal=u := hb _ (by rwa [Real.le_toNNReal_iff_coe_le ht.1])
      have hct : c (t-(A:ℝ)).toNNReal=0 := by simp [c]
      simp only [one_smul,hct] at hh'
      have hhg : HasDerivWithinAt g (2/(flow 1 c v (t-(A:ℝ))-(0:ℂ))) (Ici (A:ℝ)) t := by
        simpa only [Function.comp_def,ofReal_zero,g] using hh'
      apply hhg.congr_deriv
      rw [hright t hAt,hbt]
      dsimp only [g]
      ring
  have hYc : ContinuousOn Y (Icc 0 ((A+S:ℝ≥0):ℝ)) :=
    fun t ht => ((hd t ht).mono Icc_subset_Ici_self).continuousWithinAt
  have hYpos (t : ℝ) (ht : t∈Icc 0 ((A+S:ℝ≥0):ℝ)) : 0<(Y t).im := by
    by_cases htA : t ≤ A
    · rw [hleft t htA]
      exact surviving_flow_mem_upperHalfPlane 1 b z t ht.1
        (surviving_of_le_time 1 b z ht.1 htA hzA)
    · have hAt : A ≤ t := (le_of_not_ge htA)
      rw [hright t hAt]
      have hts : 0 ≤ t-(A:ℝ) := sub_nonneg.mpr hAt
      have htsS : t-(A:ℝ) ≤ S := by
        have hh : t ≤ (A:ℝ)+(S:ℝ) := by simpa only [NNReal.coe_add] using ht.2
        linarith
      have hp := surviving_flow_mem_upperHalfPlane 1 c v _ hts
        (surviving_of_le_time 1 c v hts htsS hvS)
      simpa only [g,add_im,ofReal_im,zero_add] using (show 0<(flow 1 c v (t-(A:ℝ))).im from hp)
  obtain ⟨r,hr,hrmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (A+S).coe_nonneg) (Complex.continuous_im.comp_continuousOn hYc)
  have hY0 : Y 0=z := by rw [hleft 0 A.coe_nonneg]; exact flow_zero 1 b z hzH
  have hraw := flow_eq_of_positive_trajectory 1 b z (A+S) (A+S).coe_nonneg Y hYc hY0
    (Y r).im (hYpos r hr) (fun t ht => hrmin ht) (fun t ht => by
      simpa only [a,div_one,Complex.ofReal_ofNat,driverValue] using
        (hd t (Ico_subset_Icc_self ht)).mono (Ici_subset_Ici.mpr ht.1))
  apply inverseFlow_eq_of_surviving 1 b (A+S) (A+S).coe_nonneg z w hraw.1
  rw [hraw.2,hright _ (by simp)]
  simp only [g,add_sub_cancel_left,hvend,add_sub_cancel]

end SLEExactGauge.Target

end

end OAI
