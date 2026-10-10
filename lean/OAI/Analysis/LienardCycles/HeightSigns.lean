import OAI.Analysis.LienardCycles.CharacteristicPositive

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ModelEndpoint
open PartialCalculus QuadraticCoordinates
lemma d_neg_of_H_neg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : H ((d,k),r) < 0) : d < 0 := by
  have hmd : StrictMono (fun d => H ((d,k),r)) := by
    apply strictMono_of_deriv_pos
    intro a; rw [(P_hasDerivAt hr).deriv]; exact QuadraticVariation.P_pos hr
  have hmk : StrictMono (fun k => H ((0,k),r)) := by
    apply strictMono_of_deriv_pos
    intro a; rw [(Q_hasDerivAt hr).deriv]; exact QuadraticVariation.Q_pos hr
  have hH0 : 0 < H ((0,k),r) := by
    have hh := hmk hk
    simpa only [(zero_data hr).2] using hh
  by_contra! hd
  have hh := hmd.monotone hd
  exact hH.not_ge (hH0.le.trans hh)

lemma Hr_pos_of_H_nonneg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : 0 ≤ H ((d,k),r)) : 0 < Hr ((d,k),r) := by
  obtain ⟨z,hz⟩ := ReferenceCharacteristic.J_surjective d k hr
  have hA : 0 ≤ ReferenceCharacteristic.A ((z,k),r) := by
    dsimp [ReferenceCharacteristic.A]
    rw [hz]
    exact div_nonneg hH hr.le
  simpa only [ReferenceCharacteristic.D,hz] using ReferenceCharacteristic.D_pos_of_A_nonneg hk hr hA

lemma w_pos_of_H_nonneg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : 0 ≤ H ((d,k),r)) : 0 < w ((d,k),r) := by
  have ha : 0 < alpha ((d,k),r) := div_pos hr (H_gap_pos hr)
  have ht := transport_Hr (d := d) (k := k) hr
  have hgap : 0 < 1-(Hr ((d,k),r))^2 := by
    have hh := abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)
    nlinarith [sq_nonneg (Hr ((d,k),r))]
  have hnon : -2*H ((d,k),r)*r*(1-(Hr ((d,k),r))^2)/(gap ((d,k),r))^2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hH) hr.le) hgap.le)
      (sq_nonneg _)
  have hpr := mul_pos hk (R_pos (d := d) (k := k) hr)
  have hHrr : 0 < Hrr ((d,k),r) :=
    pos_of_mul_pos_right (by linarith : 0 < alpha ((d,k),r)*Hrr ((d,k),r)) ha.le
  have hplus : 0 < 1+Hr ((d,k),r) := by
    have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).1
    linarith
  exact div_pos (mul_pos (by norm_num) hHrr) (mul_pos (sq_pos_of_pos (mr_pos hr)) hplus)

lemma sch_pos_of_H_neg_Hr_nonneg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : H ((d,k),r) < 0) (hHr : 0 ≤ Hr ((d,k),r)) : 0 < sch ((d,k),r) := by
  have hd := d_neg_of_H_neg hk hr hH
  have hm := m_pos (d := d) (k := k) hr
  have hn := n_pos (d := d) (k := k) hr
  have hmn : n ((d,k),r) < m ((d,k),r) := by dsimp [m,n]; linarith
  have hl : 1 ≤ ell ((d,k),r) := by
    apply (le_div_iff₀ (mr_pos hr)).mpr
    linarith
  have hl2 : 1 ≤ (ell ((d,k),r))^2 := by nlinarith
  have hbase : 0 ≤ (ell ((d,k),r))^2/(n ((d,k),r))^2-1/(m ((d,k),r))^2 := by
    have hsq : (n ((d,k),r))^2 ≤ (m ((d,k),r))^2 := sq_le_sq₀ hn.le hm.le |>.mpr hmn.le
    have hh : (1:ℝ)/(m ((d,k),r))^2 ≤ (ell ((d,k),r))^2/(n ((d,k),r))^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hm) (sq_pos_of_pos hn)).mpr
      nlinarith [mul_nonneg (sq_nonneg (m ((d,k),r))) (sub_nonneg.mpr hl2)]
    linarith
  have hkn : 0 < k*(m ((d,k),r)+n ((d,k),r)*(ell ((d,k),r))^2) := by positivity
  have hd2 : 0 ≤ d^2/2*((ell ((d,k),r))^2-1) := mul_nonneg (by positivity) (by linarith)
  have hdp : 0 ≤ -d*(1/m ((d,k),r)+(ell ((d,k),r))^2/n ((d,k),r)) := mul_nonneg (neg_nonneg.mpr hd.le) (by positivity)
  dsimp only [sch,Prod.fst] at *
  nlinarith

lemma w_nonneg_of_H_neg_Hr_nonneg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : H ((d,k),r) < 0) (hHr : 0 ≤ Hr ((d,k),r)) : 0 ≤ w ((d,k),r) := by
  have hd := d_neg_of_H_neg hk hr hH
  obtain ⟨a,ha0,har,ha⟩ : ∃ a : ℝ, 0 < a ∧ a < r ∧ Hr ((d,k),a) < 0 := by
    have he : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < a ∧ a < r ∧ Hr ((d,k),a) < 0 := by
      filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono inf_le_left,
        Hr_negative_near_zero (k := k) hd] with a ha0 har ha
      exact ⟨ha0,har,ha⟩
    exact he.exists
  let C : ℝ → ℝ := fun s => (1-Hr ((d,k),s))^2*(1+Hr ((d,k),s))/2
  have hC (s : ℝ) (hs : 0 < s) : 0 < C s := by
    have hm := mr_pos (d := d) (k := k) hs
    have hp : 0 < 1+Hr ((d,k),s) := by
      have ht := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hs)).1
      linarith
    dsimp [C]; positivity
  apply RegionBarrier.no_negative_w har
    (fun s hs => Hr_hasDerivAt (ha0.trans_le hs.1))
    (C := C) (w' := fun s => (1-Hr ((d,k),s))*(sch ((d,k),s)+(1/2)*(w ((d,k),s))^2))
    _ (fun s hs => w_deriv (ha0.trans_le hs.1)) (fun s hs => hC s (ha0.trans_le hs.1)) _ ha hH hHr
  · intro s hs
    convert! Hrr_hasDerivAt (d := d) (k := k) (ha0.trans_le hs.1) using 1
    dsimp [C,w]
    have hm := mr_pos (d := d) (k := k) (ha0.trans_le hs.1)
    have hp : 0 < 1+Hr ((d,k),s) := by
      have ht := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) (ha0.trans_le hs.1))).1
      linarith
    field_simp [ne_of_gt hm,ne_of_gt hp]
  · intro s hs hHs hHrs
    have hsch := sch_pos_of_H_neg_Hr_nonneg hk (ha0.trans_le hs.1) hHs hHrs
    exact mul_pos (mr_pos (ha0.trans_le hs.1)) (by nlinarith [sq_nonneg (w ((d,k),s))])
end QuinticLienard.ModelEndpoint

end OAI
