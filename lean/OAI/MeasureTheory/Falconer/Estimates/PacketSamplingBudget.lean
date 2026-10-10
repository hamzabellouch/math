import OAI.MeasureTheory.Falconer.Estimates.PacketParameterBounds
import OAI.MeasureTheory.Falconer.Geometry.ProjectionSampleBudget

namespace OAI

/-! The actual retained point fraction supplies the projection-sampling
budget; it is not an additional regularity assumption. -/
namespace Falconer

theorem packet_sampling_budget (N : ℕ) {κ s t E K KP KF J B m M : ℝ}
    (hκ : 0 < κ) (hs : s ≤ 1) (hgap : κ ≤ t-s)
    (hE : 1 ≤ E) (hK : 0 ≤ K) (hKup : K ≤ E) (hKP : 0 ≤ KP) (hKPup : KP ≤ E)
    (hKF : 1 ≤ KF) (hKFup : KF ≤ E) (hJ : 0 < J) (hJup : J ≤ E)
    (hB : 0 < B) (hBup : B ≤ E/(1/(2:ℝ)^N)^s)
    (hm : 1/(E*((1/(2:ℝ)^N)^s)^2) ≤ m)
    (hM : 0 < M) (hMup : M ≤ E/((1/(2:ℝ)^N)^s)^2) :
    projectedSubsetSampleConstant N s t (25*K*(4:ℝ)^s) KP
      (m/(4*J*B*(KF*(1/(2:ℝ)^N)^s*M))) ≤
        ((100:ℝ)^8*(512*(64*Real.exp 1*(1+32*projectionGapConstant κ)+100)^2))*
          ((N:ℝ)+1)^2*E^40 := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hE5 : E ≤ E^5 := by simpa only [pow_one] using pow_le_pow_right₀ hE (by norm_num : 1 ≤ 5)
  have hE51 : 1 ≤ E^5 := one_le_pow₀ hE
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδs : 0 < (1/(2:ℝ)^N)^s := Real.rpow_pos_of_pos hδ _
  have hm0 : 0 < m := (by positivity : 0 < 1/(E*((1/(2:ℝ)^N)^s)^2)).trans_le hm
  have h4 : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 4) hs
  have hKI : 25*K*(4:ℝ)^s ≤ 100*E^5 := by
    calc
      _ ≤ 25*E*4 := by gcongr
      _ ≤ _ := by nlinarith only [hE5]
  have hKPI : KP ≤ 100*E^5 := by
    have hh : E^5 ≤ 100*E^5 := by nlinarith only [hE51]
    exact hKPup.trans (hE5.trans hh)
  have hρ := (packet_parameter_bounds hδ hE hKF hKFup hJ hJup hB hBup hm hM hMup).2.2.2
  have hρ' : 1/(100*E^5) ≤ m/(4*J*B*(KF*(1/(2:ℝ)^N)^s*M)) := by
    apply le_trans _ hρ
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hE51] : 4*E^5 ≤ 100*E^5)
  have hst : s < t := by linarith only [hκ,hgap]
  have hH := projectionGapConstant_pos hκ
  have hb := projectedSubsetSampleConstant_upper N hst hs (by positivity) hKP
    (show 1 ≤ 100*E^5 by nlinarith only [hE51]) hKI hKPI
    (by positivity : 0 < m/(4*J*B*(KF*(1/(2:ℝ)^N)^s*M))) hρ' hH.le
    (planarPotentialConstant_gap hκ hs hgap)
  convert hb using 1
  ring

end Falconer

end OAI
