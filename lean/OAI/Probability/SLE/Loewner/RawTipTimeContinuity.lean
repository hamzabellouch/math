import OAI.Probability.SLE.Loewner.SmoothRawInverse
import OAI.Probability.SLE.Loewner.ReverseFlowStability

namespace OAI

/-! Interior radial approximations to the raw tip vary continuously with
time for a Lipschitz driver. The bound is uniform on each finite interval. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma gronwallBound_scale_initial (δ K c t : ℝ) :
    gronwallBound δ K (c*δ) t = δ*gronwallBound 1 K c t := by
  unfold gronwallBound
  split_ifs <;> ring

namespace Target

lemma raw_radial_time_distance (b : Driver) {L : ℝ≥0}
    (hb : LipschitzWith L (driverValue b)) (R T S : ℝ≥0)
    (hT : T ≤ R) (_hS : S ≤ R) {y : ℝ} (hy : 0 < y) :
    dist (inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I))
      (inverseFlow 1 b S ((b S : ℂ)+(y : ℂ)*I)) ≤
        ((L : ℝ)*gronwallBound 1 (4*y⁻¹^2) (2*y⁻¹^2) R+2*y⁻¹) * dist T S := by
  obtain ⟨q,hq0,hqy,hqd,heq⟩ := exists_raw_reverse_trajectory b T
    ((b T : ℂ)+(y : ℂ)*I) (by simpa [upperHalfPlane] using hy)
  obtain ⟨r,hr0,hry,hrd,her⟩ := exists_raw_reverse_trajectory b S
    ((b S : ℂ)+(y : ℂ)*I) (by simpa [upperHalfPlane] using hy)
  have hdQ (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt q
      (reverseField y (driverValue b ((T : ℝ)-t)) (q t)) (Ici 0) t := by
    rw [reverseField,reverseCenter_eq (by simpa using hqy t ht)]
    exact hqd t ht
  have hdR (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt r
      (reverseField y (driverValue b ((S : ℝ)-t)) (r t)) (Ici 0) t := by
    rw [reverseField,reverseCenter_eq (by simpa using hry t ht)]
    exact hrd t ht
  have hinit : dist (q 0) (r 0) ≤ (L : ℝ)*dist T S := by
    rw [hq0,hr0,dist_add_right]
    simpa only [driverValue,Real.toNNReal_coe,dist_eq_norm,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,NNReal.dist_eq] using
      hb.dist_le_mul (T : ℝ) (S : ℝ)
  have hsame := reverse_flow_driver_distance hy
    (fun t => driverValue b ((T : ℝ)-t)) (fun t => driverValue b ((S : ℝ)-t))
    q r (T : ℝ) (fun t ht => (hdQ t ht.1).mono Icc_subset_Ici_self)
    (fun t ht => (hdR t ht.1).mono Icc_subset_Ici_self)
    ((L : ℝ)*dist T S) hinit (fun t _ => by
      simpa only [Real.dist_eq,sub_sub_sub_cancel_right,NNReal.dist_eq] using
        hb.dist_le_mul ((T : ℝ)-t) ((S : ℝ)-t)) T ⟨T.coe_nonneg,le_rfl⟩
  have hmono := gronwallBound_mono (show 0 ≤ (L : ℝ)*dist T S by positivity)
    (show 0 ≤ 2*y⁻¹^2*((L : ℝ)*dist T S) by positivity)
    (show 0 ≤ 4*y⁻¹^2 by positivity) (show (T : ℝ) ≤ R from hT)
  have htime := (reverse_flow_lipschitz hy _ r hdR).dist_le_mul
    (T : ℝ) T.coe_nonneg (S : ℝ) S.coe_nonneg
  change dist (r (T : ℝ)) (r (S : ℝ)) ≤ (2*y⁻¹)*dist (T : ℝ) (S : ℝ) at htime
  rw [heq,her]
  calc
    dist (q T) (r S) ≤ dist (q T) (r T)+dist (r T) (r S) := dist_triangle _ _ _
    _ ≤ gronwallBound ((L : ℝ)*dist T S) (4*y⁻¹^2)
        (2*y⁻¹^2*((L : ℝ)*dist T S)) R + (2*y⁻¹)*dist T S := by
      exact add_le_add (hsame.trans hmono) (by simpa only [NNReal.coe_mk,NNReal.dist_eq,Real.dist_eq] using htime)
    _ = _ := by rw [gronwallBound_scale_initial]; ring

lemma continuous_raw_radial_time (b : Driver) {L : ℝ≥0}
    (hb : LipschitzWith L (driverValue b)) {y : ℝ} (hy : 0 < y) :
    Continuous (fun T : ℝ≥0 => inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I)) := by
  have hlocal (R : ℝ≥0) : ContinuousOn
      (fun T : ℝ≥0 => inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I)) (Iic R) := by
    have hpos : 0 ≤ (L : ℝ)*gronwallBound 1 (4*y⁻¹^2) (2*y⁻¹^2) R+2*y⁻¹ := by
      have hg := gronwallBound_mono (by norm_num : (0 : ℝ) ≤ 1)
        (show 0 ≤ 2*y⁻¹^2 by positivity) (show 0 ≤ 4*y⁻¹^2 by positivity)
        R.coe_nonneg
      rw [gronwallBound_x0] at hg
      positivity
    apply LipschitzOnWith.continuousOn (K := ⟨_,hpos⟩)
    apply LipschitzOnWith.of_dist_le_mul
    intro T hT S hS
    exact raw_radial_time_distance b hb R T S hT hS hy
  apply continuous_iff_continuousAt.mpr
  intro T
  exact (hlocal (T+1)).continuousAt (Iic_mem_nhds (by simp))

end Target
end SLEExactGauge

end

end OAI
